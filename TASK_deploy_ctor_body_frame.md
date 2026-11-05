# TASK: The constructor body's simulation premises and exit side conditions

## Meta
Status: planned
Priority: P0
Created: 2026-11-05
Location: lowering/proofs/ctorDeployLoweringFrameScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem deploy_ctor_body_frame:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    call_outcomes_ok am tx (MAP SND (call_trace es)) /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) ==>
    body_inv tops dunit.cu_context cenv (deploy_evaluation_context tops am tx) /\
    cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
    LENGTH runtime_bc + imm_len tops < dimword(:256) /\
    (nr ==> ut /\ storage_layout_safe (deploy_evaluation_context tops am tx) /\
            (deploy_evaluation_context tops am tx).nonreentrant_slot = SOME nkey) /\
    (imm_len tops <> 0 ==>
       cenv.ce_imm_alloca = SOME imm /\
       !x. imm = Var x ==> not_fresh_at st_epilogue x) /\
    ?bindings env_t env'.
      supported_stmts tops bindings body /\
      expr_sim_inv cenv (deploy_evaluation_context tops am tx) env_t
        (es0 with outcomes := SOME vs.vs_outcomes) /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t NoneT body = SOME env' /\
      EVERY (stmt_exprs_ok cenv) body /\
      call_evaluation_safe (deploy_evaluation_context tops am tx) (int_calls_stmts body)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `deploy_ctor_body_frame` is proved, with no `cheat`, and `holbuild -j4 build ctorDeployLoweringFrameTheory` passes.
2. No statement or definition outside new helper theorems changes. No new definitions, axioms, timeout overrides, or `TRY`/`ORELSE` around search tactics (`metis_tac`, `fs`, `simp` searches).
3. Helpers go in `lowering/proofs/ctorDeployLoweringFrameScript.sml` or in a new theory `lowering/proofs/ctorDeployLoweringFrame<Name>Script.sml`. Do not edit any other existing file.

## Build

```sh
holbuild -j4 build ctorDeployLoweringFrameTheory
```

## Background

The constructor body's statement simulation (`body_stmts_sim`, used through
`stmt_frag` in `lowering/proofs/ctorDeployLoweringScript.sml`) needs premises
at the body's start, and the constructor's exit (`constructor_frame_ret_ok`,
`lowering/proofs/ctorDeployLoweringFrameRetScript.sml`, and
`constructor_exit_run`, `lowering/proofs/ctorReturnFrameScript.sml`) needs side
conditions. This piece gives both, for the constructor code that
`deploy_ctor_code` names (`lowering/proofs/ctorDeployLoweringDefsScript.sml`)
and the source state `es0` at the body's start (`deploy_ctor_start`).

Where each conjunct comes from:
- `body_inv`, `ce_is_ctor`, `ce_return_pc = NONE`: the compile environment
  `package_constructor` builds (`lowering/defs/compileVyperScript.sml`) and
  `compile_register_constructor_args` extends; `body_inv` is in
  `lowering/bodySimScript.sml`. The runtime analogue for external functions is
  worth finding (grep `body_inv` in `lowering/`).
- The size bound: `deploy_imm_budget_ok` (`ctorDeployLoweringBudgetScript.sml`).
- `nr ==> ...`: a supported constructor is never nonreentrant
  (`supported_declaration_header`, `lowering/supported/supportedDeclsScript.sml`),
  and `nr` is the same in `deploy_ctor_code` and `deploy_ctor_start`.
- `not_fresh_at st_epilogue x`: `imm` is a variable allocated
  (`compile_fixed_region_with_id`) before `st_epilogue`; compile steps only
  grow the variable counter.
- `supported_stmts`, `type_stmts`, `stmt_exprs_ok`, `call_evaluation_safe`: the
  deployment typing and support checks in `deploy_source_ok`
  (`lowering/proofs/ctorDeployDefsScript.sml`, `deploy_typing_ok` in
  `lowering/e2eDeployDefsScript.sml`).
- `expr_sim_inv` at `es0 with outcomes := SOME vs.vs_outcomes`
  (`lowering/exprSimHypsDefsScript.sml`): `vs.vs_outcomes` is
  `MAP SND (call_trace es)` (`entry_venom_state`, `lowering/e2e/e2eEntryScript.sml`,
  with `gas_variant`), and `call_outcomes_ok` (a premise,
  `lowering/e2eDefsScript.sml`) gives `outcomes_accounts_typed`.
- `ce_locals_declared`, `locals_alloc_ok`: the constructor arguments registered
  by `compile_register_constructor_args` and the typing environment of the
  arguments.

## Domain Constraints

- Default proof-step limit; checkpoints and cache on.
- Out-of-scope theorems that are admitted (cheated) are allowed dependencies,
  including `deploy_imm_budget_ok` (`lowering/proofs/ctorDeployLoweringBudgetScript.sml`);
  add no admissions of your own.
- If the statement is false, stop and give a concrete counterexample and the
  smallest change to the statement that would make it true.

## Available Resources

- `lowering/proofs/ctorDeployLoweringFrameScript.sml` (target)
- `lowering/proofs/ctorDeployLoweringDefsScript.sml`, `lowering/proofs/ctorDeployDefsScript.sml`, `lowering/e2eDeployDefsScript.sml`, `lowering/e2eDefsScript.sml`
- `lowering/proofs/ctorDeployLoweringBudgetScript.sml`
- `lowering/bodySimScript.sml`, `lowering/bodySimMainScript.sml`, `lowering/exprSimHypsDefsScript.sml`, `lowering/defs/compileEnvScript.sml`, `lowering/defs/compileVyperScript.sml`
- `lowering/ctorRegisterArgsScript.sml` (constructor argument registration)
- `lowering/supported/`, `semantics/prop/vyperTypeDeploymentSoundnessScript.sml`
- `lowering/e2e/e2eEntryScript.sml`

## Notes

The statement parses: it built with `cheat` in this worktree. Many shared
ancestors are cheated locally (the commit "LOCAL OVERLAY"); that is expected.
Do not touch or revert that commit.
