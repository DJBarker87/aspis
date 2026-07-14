# Profile 23 q18/g37 frozen release

This directory is the self-contained publication bundle for the Profile 23
release completed on 2026-07-14. It contains the exact 66,367-byte proof,
public statement, 915,656-byte SBF program, 35/35 release certificate,
preflight record, finalized devnet evidence, and manuscript PDF.

Verify every byte identity and the cross-bindings among the records:

```bash
./verify.sh
```

The verifier needs Bash, `jq`, and either `sha256sum` or `shasum`. It performs
no network access.

The finalized devnet execution consumed 1,314,332 CU at slot 476,231,605:
[view transaction](https://explorer.solana.com/tx/3ofPbzRkqMEJZCM9vwKz96rLqRFtSg4d1GyqqVBEbogtwzmJodsWb2f7V4X83BLvuPXFsT6Yyf87PC1ZbLf1R7bx?cluster=devnet).

`evidence/devnet-finalized.raw.json` is the original, hash-bound executor
output. Local absolute paths inside it are inert provenance strings and have
not been rewritten.
