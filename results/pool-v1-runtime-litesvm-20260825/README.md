# Pool V1 focused runtime evidence

This directory contains a deterministic, non-networked LiteSVM harness for the
native `aspis-pool` entrypoint. It is release evidence for Pool state/CPI/ABI
plumbing only. The test verifier in `harness/mock-verifier` is an explicit
transport double and supplies no Tag-73 or cryptographic evidence.

The production Pool crate intentionally has no `declare_id!`. The harness uses
a fixed test-only program address passed to LiteSVM at load time; it does not
select or imply a deployment address. A release Pool program id, matching
client configuration, loader/upgrade-authority policy and deployed executable
identity remain mandatory before devnet or mainnet use.

No transaction produced by this harness is signed with a user key, sent to an
RPC endpoint, or deployed to any cluster.

The focused lifecycle covers:

- fresh Pool/root-page/vault initialization through real System and SPL Token
  CPIs;
- a maximum 512-byte encrypted-payload deposit;
- whole-transaction rollback after a successful Pool append and token CPI;
- read-only privilege and source/vault alias rejection without mutation;
- atomic one-input/two-output private transfer through the exact verifier CPI
  transport, followed by duplicate-nullifier rejection and rollback;
- withdrawal with change through a real SPL Token CPI;
- root-history page rollover at sequence 256 and a later private spend anchored
  in immutable page zero while page one is current;
- success return-data framing, failed-transaction return-data clearing, CU,
  rent, writable-lock overlap and exact legacy/v0+ALT transaction sizes.

The Pool ABI uses `ASIR` for initialization, `ASPD` for deposit delivery and
`ASTR` for both `ASPT` private-transfer and `ASWD` withdrawal success. `ASPT`
and `ASWD` are instruction magics, not success receipt magics.

`replay-focused.sh` verifies `MANIFEST.sha256` when present and replays only
this locked local harness. It writes `evidence.replay.json` by default so the
frozen evidence is not overwritten.
