# TASK: Reconcile recursive tuple acceptance with positive-size body dispatch

## Meta

Owner: sol. The source tuple-widening prerequisite is being integrated with
the current compiler-proof base. Its new assignable-type checks reject empty
tuple and struct variable types and provide positive layout sizes. Preserve
both that behavior and recursive tuple-target widening.

## Theorem Statement (FROZEN)

Prove the existing local helper `assign_tuple_locals_bytes_pos` in
`lowering/bodySimStmtCasesScript.sml`:

```sml
!cenv cx env es ret_ty ids e env'.
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty
    (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) =
    SOME env' ==>
  EVERY (\id. !ty. FLOOKUP env.var_types id = SOME ty ==>
                   0 < type_memory_bytes cenv ty) ids
```

Preserve and prove the existing combined `body_assign_tuple_case` statement:

```sml
!cx gs e.
  (!s'' tv t s'3' v t'.
     eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
     body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e ==>
  body_stmt_ok cx (Assign (TupleTarget gs) e)
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
All other existing exported theorem statements and all executable/source
definitions are frozen too. Existing proofs remain in place as the starting
point; do not replace them with admissions.

## Completion Criteria

- Repair the unchanged helper/caller proofs and any directly affected source
  tuple-typing proofs, with no new admission or axiom.
- Preserve the recursive `atarget_accepts` definition, nonempty assignable
  tuple/struct checks, and original exported soundness/storage contracts.
- Build the listed theories with the default 2.5s proof-step budget.
- Commit checked work with `Bot: sol (OpenAI GPT-6.1 Sol)`.
- Report inherited admissions separately; their removal is outside this repair.

## Build

`holbuild -j2 build bodySimStmtCasesTheory vyperTypeArgFitsTheory vyperTupleWideningTestTheory`

The statements are unchanged from previously parsed source, but the merged
body helper has not yet been rebuilt against recursive target acceptance.
The owner performs forced CI-mode replay, the dependency audit and PR review.

## Background

The new base's tuple-local positivity proof reconstructs exact target typing
from `atarget_accepts`. Recursive acceptance also permits widened leaves, so
that proof no longer follows the checker. The merged case dispatch retains
the exact-typing guard for the existing equal-layout memory fragment and its
matching negation in the existing residual. The combined body theorem remains
unchanged. No new source, stage, body or allocation hypothesis is available.

## Domain Constraints

- Edit proofs in `bodySimStmtCasesScript.sml` and directly affected source
  typing proof theories; add consumed local proof helpers if needed.
- Do not edit compiler/source definitions, add supported-subset checks, or
  strengthen any existing statement. Report a missing contract instead.
- Keep the existing exact-target guard/residual partition. General aggregate
  memory widening has a separate unfinished proof; do not claim it here.
- No new final admission, TRY/ORELSE around search, timeout override,
  interactive HOL session or bytecode parity rollup.
- Other worktrees have active proof writers. Do not edit or import from them.
- Report unrelated ancestor failures before duplicating their proof repairs.

## Available Resources

- `lowering/bodySimStmtCasesScript.sml`: positivity helper and tuple dispatch.
- `semantics/type/vyperTypeSystemScript.sml`: recursive acceptance and
  assignable-type positivity.
- `semantics/prop/vyperTypeArgFitsScript.sml`: target/widening properties.
- `semantics/prop/vyperTypeEnvScript.sml`: target/environment typing.
- `lowering/exprSimAggregateLayoutScript.sml` and `exprSimHypsScript.sml`:
  runtime layout and memory-size properties.
- `lowering/bodyStorageCasesScript.sml` and `bodyStoragePreservationScript.sml`:
  existing recursive-acceptance consumers and exact-target wrappers.
- `tests/vyperTupleWideningTestScript.sml`: nested widening regression.

## Notes

This is a proof migration after merging the base, not a change to what the
body theorem accepts. The general copy, typed statement fragments and their
new body theorem remain separate unfinished work.
