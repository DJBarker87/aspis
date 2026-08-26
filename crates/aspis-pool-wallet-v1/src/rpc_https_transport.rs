//! Hardened exact-byte HTTPS transport for Pool V1 JSON-RPC.
//!
//! Typed request construction and response decoding remain in `rpc_json` and
//! `relayer_rpc_json`. This layer only binds one manifest provider identity to
//! one canonical HTTPS endpoint and returns bounded response bytes. It never
//! logs or exposes endpoint paths/query strings, follows redirects, retries a
//! write, accepts plaintext HTTP, or relies on ambient proxy configuration.

use std::{fmt, io::Read as _, time::Duration};

use reqwest::{
    blocking::Client,
    header::{ACCEPT, CONTENT_LENGTH, CONTENT_TYPE, USER_AGENT},
    redirect::Policy,
    retry, Url,
};
use sha2::{Digest as _, Sha256};

use crate::relayer_rpc_quorum::{ExactProviderRpcExchangeV1, ExactTwoProviderRelayerRpcV1};

pub const RPC_HTTPS_PROVIDER_ID_DOMAIN_V1: &[u8] = b"aspis:pool-v1:rpc-https-provider:sha256:v1";
pub const RPC_HTTPS_MAX_RESPONSE_BYTES_V1: usize = 64 * 1024 * 1024;
const RPC_HTTPS_USER_AGENT_V1: &str = "aspis-pool-v1-operator/1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RpcHttpsTransportErrorV1 {
    InvalidEndpoint,
    ProviderIdMismatch,
    InvalidTimeout,
    EmptyRequest,
    InvalidResponseLimit,
    ClientConstruction,
    TransportFailure,
    HttpStatus(u16),
    InvalidContentType,
    ResponseTooLarge,
    EmptyResponse,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RpcHttpsQuorumTransportErrorV1 {
    ProviderOrderMismatch,
    Provider {
        provider_index: u8,
        error: RpcHttpsTransportErrorV1,
    },
    WorkerPanicked {
        provider_index: u8,
    },
}

/// Derive the manifest provider identity from the exact normalized HTTPS URL.
/// This binds TLS authentication to the otherwise opaque provider ID consumed
/// by the two-provider quorum. URL credentials and fragments are forbidden;
/// path/query API tokens remain private because only this digest is exposed.
pub fn rpc_https_provider_id_v1(endpoint: &str) -> Result<[u8; 32], RpcHttpsTransportErrorV1> {
    let endpoint = canonical_https_endpoint_v1(endpoint)?;
    let mut hasher = Sha256::new();
    hasher.update(RPC_HTTPS_PROVIDER_ID_DOMAIN_V1);
    hasher.update(
        u32::try_from(endpoint.as_str().len())
            .map_err(|_| RpcHttpsTransportErrorV1::InvalidEndpoint)?
            .to_le_bytes(),
    );
    hasher.update(endpoint.as_str().as_bytes());
    Ok(hasher.finalize().into())
}

/// One exact provider endpoint pinned by the authenticated release manifest.
pub struct ExactHttpsRpcProviderV1 {
    provider_id: [u8; 32],
    endpoint: Url,
    client: Client,
}

impl fmt::Debug for ExactHttpsRpcProviderV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ExactHttpsRpcProviderV1")
            .field("provider_id", &self.provider_id)
            .field("endpoint", &"<redacted>")
            .finish_non_exhaustive()
    }
}

impl ExactHttpsRpcProviderV1 {
    pub fn new(
        provider_id: [u8; 32],
        endpoint: &str,
        timeout: Duration,
    ) -> Result<Self, RpcHttpsTransportErrorV1> {
        if timeout.is_zero() || timeout > Duration::from_secs(120) {
            return Err(RpcHttpsTransportErrorV1::InvalidTimeout);
        }
        let endpoint = canonical_https_endpoint_v1(endpoint)?;
        if provider_id == [0u8; 32] || provider_id != rpc_https_provider_id_v1(endpoint.as_str())? {
            return Err(RpcHttpsTransportErrorV1::ProviderIdMismatch);
        }
        let connect_timeout = timeout.min(Duration::from_secs(15));
        let client = Client::builder()
            .https_only(true)
            .no_proxy()
            .redirect(Policy::none())
            .retry(retry::never())
            .connect_timeout(connect_timeout)
            .timeout(timeout)
            .build()
            .map_err(|_| RpcHttpsTransportErrorV1::ClientConstruction)?;
        Ok(Self {
            provider_id,
            endpoint,
            client,
        })
    }

    pub fn provider_id(&self) -> &[u8; 32] {
        &self.provider_id
    }

    /// Submit the exact caller-supplied JSON bytes once and return the exact
    /// bounded response bytes. Retry policy belongs above this method so a
    /// sendTransaction request is never silently replayed by the HTTP client.
    pub fn post_exact_json_v1(
        &self,
        request_json: &[u8],
        max_response_bytes: usize,
    ) -> Result<Vec<u8>, RpcHttpsTransportErrorV1> {
        if request_json.is_empty() {
            return Err(RpcHttpsTransportErrorV1::EmptyRequest);
        }
        if max_response_bytes == 0 || max_response_bytes > RPC_HTTPS_MAX_RESPONSE_BYTES_V1 {
            return Err(RpcHttpsTransportErrorV1::InvalidResponseLimit);
        }
        let response = self
            .client
            .post(self.endpoint.clone())
            .header(CONTENT_TYPE, "application/json")
            .header(ACCEPT, "application/json")
            .header(USER_AGENT, RPC_HTTPS_USER_AGENT_V1)
            .body(request_json.to_vec())
            .send()
            .map_err(|_| RpcHttpsTransportErrorV1::TransportFailure)?;
        let status = response.status();
        if !status.is_success() {
            return Err(RpcHttpsTransportErrorV1::HttpStatus(status.as_u16()));
        }
        if let Some(length) = response
            .headers()
            .get(CONTENT_LENGTH)
            .and_then(|value| value.to_str().ok())
            .and_then(|value| value.parse::<u64>().ok())
        {
            if length > max_response_bytes as u64 {
                return Err(RpcHttpsTransportErrorV1::ResponseTooLarge);
            }
        }
        let content_type = response
            .headers()
            .get(CONTENT_TYPE)
            .and_then(|value| value.to_str().ok())
            .ok_or(RpcHttpsTransportErrorV1::InvalidContentType)?;
        if !content_type
            .split(';')
            .next()
            .is_some_and(|value| value.trim().eq_ignore_ascii_case("application/json"))
        {
            return Err(RpcHttpsTransportErrorV1::InvalidContentType);
        }

        let maximum_read = u64::try_from(max_response_bytes)
            .map_err(|_| RpcHttpsTransportErrorV1::InvalidResponseLimit)?
            .saturating_add(1);
        let mut body = Vec::with_capacity(max_response_bytes.min(64 * 1024));
        response
            .take(maximum_read)
            .read_to_end(&mut body)
            .map_err(|_| RpcHttpsTransportErrorV1::TransportFailure)?;
        if body.len() > max_response_bytes {
            return Err(RpcHttpsTransportErrorV1::ResponseTooLarge);
        }
        if body.is_empty() {
            return Err(RpcHttpsTransportErrorV1::EmptyResponse);
        }
        Ok(body)
    }
}

/// Exact request/response bytes from the startup-pinned provider pair. The
/// request is retained inside the sealed result so callers cannot associate
/// either response with different bytes before invoking a quorum decoder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactTwoProviderRpcResponsesV1 {
    provider_ids: [[u8; 32]; 2],
    request_json: Vec<u8>,
    response_json: [Vec<u8>; 2],
}

impl ExactTwoProviderRpcResponsesV1 {
    pub fn provider_ids(&self) -> &[[u8; 32]; 2] {
        &self.provider_ids
    }

    pub fn request_json(&self) -> &[u8] {
        &self.request_json
    }

    pub fn response_json(&self, provider_index: usize) -> Option<&[u8]> {
        self.response_json.get(provider_index).map(Vec::as_slice)
    }

    pub fn exchanges_v1(&self) -> [ExactProviderRpcExchangeV1<'_>; 2] {
        [
            ExactProviderRpcExchangeV1::new(
                self.provider_ids[0],
                &self.request_json,
                &self.response_json[0],
            ),
            ExactProviderRpcExchangeV1::new(
                self.provider_ids[1],
                &self.request_json,
                &self.response_json[1],
            ),
        ]
    }
}

/// Parallel exact-byte transport for the same canonical provider pair pinned
/// by `ExactTwoProviderRelayerRpcV1` at successful operator startup.
pub struct ExactTwoProviderHttpsTransportV1 {
    providers: [ExactHttpsRpcProviderV1; 2],
}

impl fmt::Debug for ExactTwoProviderHttpsTransportV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ExactTwoProviderHttpsTransportV1")
            .field(
                "provider_ids",
                &[
                    *self.providers[0].provider_id(),
                    *self.providers[1].provider_id(),
                ],
            )
            .finish_non_exhaustive()
    }
}

impl ExactTwoProviderHttpsTransportV1 {
    pub fn new(
        providers: [ExactHttpsRpcProviderV1; 2],
        quorum: &ExactTwoProviderRelayerRpcV1,
    ) -> Result<Self, RpcHttpsQuorumTransportErrorV1> {
        if providers[0].provider_id() != &quorum.provider_ids()[0]
            || providers[1].provider_id() != &quorum.provider_ids()[1]
        {
            return Err(RpcHttpsQuorumTransportErrorV1::ProviderOrderMismatch);
        }
        Ok(Self { providers })
    }

    pub fn provider_ids(&self) -> [[u8; 32]; 2] {
        [
            *self.providers[0].provider_id(),
            *self.providers[1].provider_id(),
        ]
    }

    /// Submit one immutable request to both providers concurrently. There is
    /// no hidden retry; disagreement and retry scheduling remain explicit at
    /// the operator layer.
    pub fn post_both_exact_json_v1(
        &self,
        request_json: &[u8],
        max_response_bytes: usize,
    ) -> Result<ExactTwoProviderRpcResponsesV1, RpcHttpsQuorumTransportErrorV1> {
        let (first, second) = std::thread::scope(|scope| {
            let first = scope
                .spawn(|| self.providers[0].post_exact_json_v1(request_json, max_response_bytes));
            let second = scope
                .spawn(|| self.providers[1].post_exact_json_v1(request_json, max_response_bytes));
            (first.join(), second.join())
        });
        let first = first
            .map_err(|_| RpcHttpsQuorumTransportErrorV1::WorkerPanicked { provider_index: 0 })?
            .map_err(|error| RpcHttpsQuorumTransportErrorV1::Provider {
                provider_index: 0,
                error,
            })?;
        let second = second
            .map_err(|_| RpcHttpsQuorumTransportErrorV1::WorkerPanicked { provider_index: 1 })?
            .map_err(|error| RpcHttpsQuorumTransportErrorV1::Provider {
                provider_index: 1,
                error,
            })?;
        Ok(ExactTwoProviderRpcResponsesV1 {
            provider_ids: self.provider_ids(),
            request_json: request_json.to_vec(),
            response_json: [first, second],
        })
    }
}

fn canonical_https_endpoint_v1(endpoint: &str) -> Result<Url, RpcHttpsTransportErrorV1> {
    let endpoint = Url::parse(endpoint).map_err(|_| RpcHttpsTransportErrorV1::InvalidEndpoint)?;
    if endpoint.scheme() != "https"
        || endpoint.host_str().is_none()
        || !endpoint.username().is_empty()
        || endpoint.password().is_some()
        || endpoint.fragment().is_some()
        || endpoint.cannot_be_a_base()
    {
        return Err(RpcHttpsTransportErrorV1::InvalidEndpoint);
    }
    Ok(endpoint)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        operator_startup::{
            provider_set_digest_v1, FinalizedReleaseCheckpointV1, OperatorStartupReceiptV1,
        },
        scan_state::FinalizedChainPointV1,
    };

    #[test]
    fn provider_identity_pins_normalized_https_endpoint_without_exposure() {
        let canonical = "https://rpc.example.invalid/solana?token=secret";
        let provider_id = rpc_https_provider_id_v1(canonical).unwrap();
        let provider =
            ExactHttpsRpcProviderV1::new(provider_id, canonical, Duration::from_secs(30)).unwrap();
        assert_eq!(provider.provider_id(), &provider_id);
        let debug = format!("{provider:?}");
        assert!(!debug.contains("secret"));
        assert!(!debug.contains("rpc.example.invalid"));

        assert_eq!(
            ExactHttpsRpcProviderV1::new([0x55; 32], canonical, Duration::from_secs(30))
                .unwrap_err(),
            RpcHttpsTransportErrorV1::ProviderIdMismatch
        );
        assert_eq!(
            rpc_https_provider_id_v1("http://rpc.example.invalid"),
            Err(RpcHttpsTransportErrorV1::InvalidEndpoint)
        );
        assert_eq!(
            rpc_https_provider_id_v1("https://user:password@rpc.example.invalid"),
            Err(RpcHttpsTransportErrorV1::InvalidEndpoint)
        );
        assert_eq!(
            rpc_https_provider_id_v1("https://rpc.example.invalid/#fragment"),
            Err(RpcHttpsTransportErrorV1::InvalidEndpoint)
        );
    }

    #[test]
    fn provider_pair_must_equal_the_startup_quorum_order() {
        let mut endpoints = [
            (
                rpc_https_provider_id_v1("https://one.example.invalid/rpc").unwrap(),
                "https://one.example.invalid/rpc",
            ),
            (
                rpc_https_provider_id_v1("https://two.example.invalid/rpc").unwrap(),
                "https://two.example.invalid/rpc",
            ),
        ];
        endpoints.sort_by_key(|entry| entry.0);
        let provider_ids = [endpoints[0].0, endpoints[1].0];
        let startup = OperatorStartupReceiptV1::test_only_v1(
            [0x31; 32],
            provider_set_digest_v1(&provider_ids),
            FinalizedReleaseCheckpointV1 {
                point: FinalizedChainPointV1::new(100, [0x32; 32]).unwrap(),
                pool_state_sha256: [0x33; 32],
                root_sequence: 7,
                root: [0x34; 32],
            },
        );
        let quorum = ExactTwoProviderRelayerRpcV1::new(provider_ids, &startup).unwrap();
        let providers = [
            ExactHttpsRpcProviderV1::new(endpoints[0].0, endpoints[0].1, Duration::from_secs(30))
                .unwrap(),
            ExactHttpsRpcProviderV1::new(endpoints[1].0, endpoints[1].1, Duration::from_secs(30))
                .unwrap(),
        ];
        let transport = ExactTwoProviderHttpsTransportV1::new(providers, &quorum).unwrap();
        assert_eq!(transport.provider_ids(), provider_ids);

        let reversed = [
            ExactHttpsRpcProviderV1::new(endpoints[1].0, endpoints[1].1, Duration::from_secs(30))
                .unwrap(),
            ExactHttpsRpcProviderV1::new(endpoints[0].0, endpoints[0].1, Duration::from_secs(30))
                .unwrap(),
        ];
        assert_eq!(
            ExactTwoProviderHttpsTransportV1::new(reversed, &quorum).unwrap_err(),
            RpcHttpsQuorumTransportErrorV1::ProviderOrderMismatch
        );
    }
}
