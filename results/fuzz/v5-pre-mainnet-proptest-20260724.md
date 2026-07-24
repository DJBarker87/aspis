# V5 pre-mainnet property-test run

This run exercised the committed parser, field, dispatch, and proof-account
lifecycle harnesses at commit
`bf4069b43a57f32330e30ceaf30ab5e2a3324b54`.

The tests ran from a detached temporary clone with Cargo locked and offline.
Failure persistence was disabled so the campaign could not write into the
source tree.

| Harness | Generated cases per property | Seed | Result |
| --- | ---: | ---: | --- |
| `aspis-core/tests/fuzz_parser.rs` | 8,192 | 2026072401 | pass |
| `aspis-core/tests/fuzz_field.rs` | 8,192 | 2026072402 | pass |
| `aspis-verifier/tests/fuzz_dispatch.rs` | 8,192 | 2026072403 | pass |
| `aspis-verifier/tests/fuzz_lifecycle.rs` | 8,192 | 2026072404 | pass |

The four harnesses contain 15 generated properties, for 122,880 generated
cases in total. A three-case trace first confirmed that `PROPTEST_CASES`
overrode each harness's default case count.

The same clone also passed:

- the three exact Tag-67 transaction-byte tests;
- the 14 tests selected by `adversarial_account_aliasing`;
- the 14 tests selected by `without_mutation`.

These are deterministic property-based and hostile-path tests, not a
coverage-guided libFuzzer campaign.
