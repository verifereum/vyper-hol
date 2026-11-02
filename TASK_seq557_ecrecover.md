# TASK: Repair the ecrecover typing prerequisite at the default timeout

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: lowering/exprSimPrecompilesScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem evaluate_ecrecover_typed[local]:
  value_has_type (BaseTV (BytesT (Fixed 32))) vh /\
  EVERY (\tv. (?k. tv = BaseTV (UintT k) /\ k <= 256) \/
                tv = BaseTV (BytesT (Fixed 32))) [tv;tr;ts] /\
  value_has_type tv va /\ value_has_type tr ra /\ value_has_type ts sa ==>
  evaluate_ecrecover [vh;va;ra;sa] =
    INL (AddressV (case vfmExecution$ecrecover
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) vh)
      (w2n (typed_val_to_w256 tv va))
      (w2n (typed_val_to_w256 tr ra))
      (w2n (typed_val_to_w256 ts sa)) of NONE => 0w | SOME addr => addr))
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All existing theorem statements, attributes and executable definitions are frozen.

## Completion Criteria

- `holbuild -j2 build exprSimPrecompilesTheory` succeeds at the default 2.5s tactic timeout.
- No new admissions or axioms. Existing unrelated admissions remain unchanged.
- Restrict changes to proof performance in this theory; report any later prerequisite failure without broadening scope.

## Build

```sh
holbuild -j2 build exprSimPrecompilesTheory
```

## Background

Final fresh replay for module immutable simulation reached an existing CASE_TAC step that exceeds 2.5s after the ecrecover evaluator unfolds, across eight typed argument cases. A short explicit-case rewrite failed to match a subterm. Its failing proof remains in the source. This is a proof-only performance migration; the statement has already parsed in both builds.

## Domain Constraints

- Keep the default timeout. Do not skip proof steps or catch tactic timeouts with TRY/ORELSE.
- No executable changes, new assumptions, supported-subset changes or theorem restatements.
- Use holbuild; no HOL REPL.
- Other task files and proofs belong to the owner. Only exprSimPrecompilesScript.sml may be edited.
- Commit only the proof repair, with trailer `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- lowering/exprSimPrecompilesScript.sml: target, ecrecover_arg_typed_encoding and adjacent execution proofs.
- lowering/defs/valueEncodingScript.sml: typed_val_to_w256.
- semantics/vyperValueScript.sml and semantics/vyperValueOperationScript.sml: runtime values and builtin evaluation.
- semantics/prop/vyperTypeValuesScript.sml: value_has_type.
- lowering/emitHelperPropsScript.sml: instruction helpers used elsewhere in this theory.

## Notes

Scope is the prerequisite theory only. The owner performs final fresh checks and CI. Build scheduling may wait for shared machine memory.
An independent statement check returned PROVABLE against the evaluator, value typing and argument encoding definitions.
