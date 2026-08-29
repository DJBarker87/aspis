# Aeneas loop-input identity fix

The unmodified production `finish_onefold_relation` reached Aeneas' loop
matcher and aborted before emitting Lean:

```text
Could not find symbolic value @27 in src_to_joined_map
Source: crates/aspis-core/src/v6_transcript.rs, former lines 782:4-836:1
Compiler source: src/interp/InterpJoin.ml, former line 1968
```

The comment immediately above that branch already specifies the intended
semantics: symbolic values absent from the partial source-to-joined map use
the identity substitution.  The old interface passed only symbolic IDs, so
the missing-map branch no longer had the symbolic value's type and raised an
error instead.

`aeneas-d860ac47-loop-input-identity.patch` retains each existing complete
`symbolic_value` through `InterpLoops` and `InterpStatements`.  The missing
branch can therefore call the existing
`ValuesUtils.mk_tvalue_from_symbolic_value`; mapped branches are unchanged.
No Rust source, LLBC item, generated result branch, or protocol value is
modified.

The patch applies after the three prior audited d860ac47 compatibility
patches.  A clean static replay produced Git tree
`c4385d45cd32b6c6bb59de3659aaadffe3239a21` and `git diff --check` passed.
The focused build and regression translation are recorded in
`../REPLAY-RESULT.md` after the NUC memory gate opens.
