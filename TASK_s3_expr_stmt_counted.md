# TASK: Counted memory simulation for expression statements

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/stmtMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_expr_stmt_frag_ok_mem:
  !d ctx func cx lctx RetQ cenv ty e es.
    expr_vv_sim_mem ctx func cenv cx (expr_type e) e es /\
    (!gs sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      (eval_stmt cx (Expr e)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. Prove the named counted memory expression-statement composer, retaining all
   existing successful proof code while migrating it.
2. Build stmtMemoryTheory with the existing strict kernel gate intact.
3. No new definitions, axioms, admissions, stage hypotheses or weakened posts.

## Build

`holbuild -j2 build stmtMemoryTheory`

The changed statement has not yet been parsed: its existing proof is retained
and ancestors need the counted join. Independent audit: PROVABLE at composition
level, matching the canonical ordinary stmtSimExpr source-action schema.
Owner preflight reached stmtMemory after checking shared ancestors. It first
reported undeclared cenv_top_ext_refl/expr_exit_INR_type; both are existing
stmtSimProps exports, now imported explicitly. The old unused exprSimHyps
proof import was removed to avoid unrelated unported ordinary operator proofs.
Proceed from this source; the existing composer proof still needs migration.

## Background

expr_vv_sim_mem and stmt_frag_mem now use actual counted source actions. The
nontermination callback quantifies over selected source GAS readings. The
canonical common nil/pass/cons roots already exist; do not recreate them.
This job owns only the expression-statement composer, not the universal body.

## Domain Constraints

No new axiom, admission, timeout override or TRY/ORELSE search wrapper.
Keep proof steps, cache and checkpoints enabled. No holbuild run/repl.
Search before adding helpers: export/move existing facts rather than duplicating
local or renamed copies. Preserve theory-local simp scope when exporting.
No source-semantics, executable compiler or supported-program changes.
No new stage/program safety premise, oracle equality or no-GAS exclusion.
Retain complete posts, local/alloca preservation, allocation history/frontier,
caller-owned return buffers and arbitrary RetQ for every terminal gas tail.
Finite storage observations concern the selected actual source execution;
all-oracle gas_admissible covers result shape only. The shared selected-run
finite-storage selector is unresolved: do not silently add all-gas H goodness,
move it into admissibility or claim source-trace transport through gas_obs.

Edit only lowering/stmtMemoryScript.sml and required imports/build roots.
Existing local helpers in stmtSimExpr/stmtSimProps may be exported with their
statements/proofs and local simp scope unchanged, to avoid duplicate proofs.
Other functional source proofs and shared definitions are read-only.
Do not edit bodyMemory, bodyMemoryPreds or other additive body consumers.
Keep all original successful proof code available while replacing its old
fixed-result proof with the counted one; comments may preserve obsolete code.
Do not restore the removed nil/pass/cons copies. Use original public owners.

## Available Resources

- lowering/stmtSimExprScript.sml: canonical ordinary counted sibling and its
  existing source admissibility, exception, exemption and post helpers.
- lowering/stmtSimSeqMemScript.sml and stmtSimJumpMemScript.sml: examples of
  mode-T composition preserving caller buffers/history/frontier.
- lowering/exprSimMemDefsScript.sml, stmtSimDefsScript.sml: frozen shared defs.
- lowering/gasOutcomeScript.sml, gasSummaryComposeScript.sml,
  gasSummaryScript.sml, gasExemptCertScript.sml: counted combinators.
- lowering/bodyMemoryDefsScript.sml: return-buffer frame transport.

## Notes

Ordinary helpers must be reused/exported, not duplicated under memory-prefixed
names. Actual counted paths are required; a conditional frag_exec_mem witness
is not enough. Keep arbitrary RetQ and every terminal source gas tail.
