# Profile23 demo cost and refund lifecycle

The mainnet demonstration is an ephemeral loader-v3 deployment. It retains its
upgrade authority, runs the proof transition, records finalized evidence, and
then closes the ProgramData account. The temporary upload buffer is recycled
into ProgramData during deployment; it is not a second simultaneous rent
deposit.

For an SBF image of 921,848 bytes, the mainnet-beta rent schedule observed on
2026-07-14 gives:

| Component | Lamports | SOL | Recovery |
|---|---:|---:|---|
| Temporary loader buffer | 6,417,210,480 | 6.417210480 | Automatically drained before ProgramData creation |
| ProgramData | 6,417,266,160 | 6.417266160 | Recovered by loader-v3 program closure |
| Program account / ID | 1,141,440 | 0.001141440 | Not recoverable under loader-v3 |
| Proof account | 449,720,400 | 0.449720400 | Recovered atomically by successful tag65, or explicitly by tag64 |
| Minimal one-byte replay probe | 1,176,240 | 0.001176240 | Recovered explicitly by tag 64 |
| Pool account | 1,224,960 | 0.001224960 | Retained as finalized demo state |
| Nullifier marker | 1,392,000 | 0.001392000 | Retained as finalized demo state |

With a 0.05 SOL upper bound reserved for every transaction fee, the exact
budget formulas are:

```text
fresh working capital
  = max(buffer, ProgramData) + Program + Proof + Replay + Pool + Nullifier + fee ceiling
  = 6.921921200 SOL

refunded after tag65, tag64, and ProgramData closure
  = ProgramData + Proof + Replay
  = 6.868162800 SOL

maximum retained or spent
  = Program + Pool + Nullifier + fee ceiling
  = 0.053758400 SOL
```

The fee ceiling is deliberately much larger than the observed fee load. The
expected complete-demo net is approximately 0.009 SOL, including the three
small retained accounts, but only finalized transaction metadata is used for
the published result.

## Fail-closed USD ceiling

The mainnet readiness command does not accept an operator-entered price. It
fetches the public SOL-USD ticker from the pinned Coinbase Exchange endpoint
after this explicit network acknowledgement:

```text
ASPIS_PROFILE23_FETCH_SOL_USD_QUOTE=I_ACKNOWLEDGE_THE_PINNED_COINBASE_SOL_USD_QUOTE_FETCH
```

The quote must be no more than one hour old. The gate uses the greater of the
reported trade and ask prices, then adds a 10% price safety margin. Integer
arithmetic converts the fixed USD 20.00 ceiling into lamports, rounding the
allowed lamports down and the projected USD cost up. Readiness fails if the
complete 0.053758400 SOL worst-case budget exceeds USD 20.00 at the adjusted
price. The raw response hash, quote time, fetch time, observed price, and
adjusted price are recorded.

## Required order

1. Generate a fresh disposable Program ID and retain a dedicated upgrade
   authority. Never deploy with `--final`.
2. Deploy the exact frozen SBF with no unused ProgramData headroom. Use zero
   priority fee and a bounded signing attempt count.
3. Run the proof lifecycle. Successful tag65 must close the proof account and
   refund its complete balance in the same transaction as the pool/nullifier
   transition.
4. Close every abandoned sealed proof with tag 64. An initialized partial
   proof is recovered by putting tag 62 and tag 64 in one atomic transaction,
   so no incomplete sealed account can commit. Close any failed loader buffer
   with `solana program close <BUFFER>`.
5. Save and durably copy an immutable, hashed pre-close evidence artifact.
6. Close ProgramData to the payer with
   `solana program close <PROGRAM_ID> --bypass-warning`.
7. Verify the ProgramData account is absent. Write a linked post-close receipt
   and independently reconcile its exact refund from finalized transaction
   `preBalances`, `postBalances`, and `fee`, along with every other submitted
   transaction fee.

Program closure is last because it permanently disables the disposable
Program ID and makes any remaining program-owned state inaccessible.
