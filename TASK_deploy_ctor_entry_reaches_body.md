# TASK: Deploy constructor entry reaches the body start

## Meta
Status: planned
Priority: P0
Created: 2026-11-05
Location: lowering/proofs/ctorDeployLoweringEntryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem deploy_ctor_entry_reaches_body:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut nr' body' am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) ==>
    nr' = nr /\ body' = body /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    ?s0.
      stmt_state_rel dunit.cu_context func cenv (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      !fuel r. run_from fuel dunit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' dunit.cu_context vs = r
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `deploy_ctor_entry_reaches_body` is proved, with no `cheat`, and `holbuild -j4 build ctorDeployLoweringEntryTheory` passes.
2. No statement or definition outside new helper theorems changes. No new definitions, axioms, timeout overrides, or `TRY`/`ORELSE` around search tactics (`metis_tac`, `fs`, `simp` searches).
3. Helpers go in `lowering/proofs/ctorDeployLoweringEntryScript.sml` or in a new theory `lowering/proofs/ctorDeployLoweringEntry<Name>Script.sml`. Do not edit any other existing file.

## Build

```sh
holbuild -j4 build ctorDeployLoweringEntryTheory
```

## Background

`deploy_ctor_entry_reaches_body` is one leaf of `deploy_unit_execution_correct`
(`lowering/proofs/ctorDeployLoweringScript.sml`): the deployment counterpart of
the runtime's `external_entry_reaches_body`. The deploy unit's `__deploy`
function (`deploy_ctor_code_def`, `lowering/proofs/ctorDeployLoweringDefsScript.sml`)
runs, in order: the payable check (CALLVALUE/ISZERO/ASSERT unless payable), the
immutables fixed region (`compile_fixed_region_with_id`, when `imm_len tops > 0`),
`compile_register_constructor_args` (ABI-decodes the constructor arguments from
the data section with DLOAD into ALLOCA'd buffers), the nonreentrant lock
(when `nr`), then `fresh_label "ctor_exit"`, leaving the body start `sa`.

The theorem says: from the deploy entry state (`deploy_entry_state`, up to
`gas_variant`), the Venom run reaches `sa` in a state `s0` related by
`stmt_state_rel` to the source's body-start state `es0`
(`deploy_ctor_start`), and every non-Error result from `s0` is a result of
`run_context` from the entry.

Facts already checked on the statement:
- `immutables_rel`: `cenv.ce_is_ctor` is true, so the clause reads memory; the
  fresh region is zero and `initial_immutables_module` gives default values.
- `vs_pending_deletions`: `deploy_state_rel_def` now has
  `es.rollback.toDelete = am.pending_deletions`, and `am.pending_deletions = []`.
- No GAS opcode runs in the prefix, so gas readings are unchanged.
- `alloca_room` follows from `deploy_imm_budget_ok`
  (`lowering/proofs/ctorDeployLoweringBudgetScript.sml`) and
  `ctorDeployMemoryFrontier`.
- `fmp_room` is proved: `deploy_ctor_entry_fmp_room`
  (`lowering/proofs/ctorDeployLoweringEntryFmpScript.sml`) gives it for every
  state of `func`, from `supported_program tops` (part of `deploy_source_ok`)
  and `deploy_ctor_code`, since the deploy unit has no DALLOCA.
- The argument decode: the data section equals the constructor argument bytes
  (`constructor_args_encode`, `lowering/e2eDeployDefsScript.sml`); `data_size = 0`
  disables the decoder's upper-bound check, which is harmless for a
  well-formed encoding.


## Domain Constraints

- Default proof-step limit; checkpoints and cache on.
- Out-of-scope theorems that are admitted (cheated) are allowed dependencies,
  including `deploy_imm_budget_ok` (`lowering/proofs/ctorDeployLoweringBudgetScript.sml`);
  add no admissions of your own.
- If the statement is false, stop and give a concrete counterexample and the
  smallest change to the statement that would make it true.

## Available Resources

- `lowering/proofs/ctorDeployLoweringEntryScript.sml` (target)
- `lowering/proofs/ctorDeployLoweringEntryFmpScript.sml` (`fmp_room` for the constructor function)
- `lowering/proofs/ctorDeployLoweringDefsScript.sml` (`deploy_ctor_code_def`, `deploy_ctor_start_def`, `deploy_source_ok_def`)
- `lowering/proofs/ctorDeployDefsScript.sml` (`deploy_phases_def`, `deploy_entry_state_def`)
- `lowering/e2eDeployDefsScript.sml` (`deploy_state_rel_def`, `constructor_args_encode_def`)
- `lowering/proofs/ctorDeployEntryScript.sml`, `lowering/proofs/ctorDeployMemoryFrontierScript.sml`, `lowering/proofs/deployEntryLayoutScript.sml` (facts about the deploy entry state)
- `lowering/defs/compileEnvScript.sml` (`state_rel_def`, `immutables_rel_def`, `local_ptrs_rel_def`), `lowering/exprLoweringPropsScript.sml` (`stmt_state_rel_def`, `alloca_room_def`, `fmp_room_def`)
- `lowering/entryLocalsScript.sml` (`compile_register_constructor_args_reserved` and argument registration facts), `lowering/abiDecoder*Script.sml`, `lowering/defs/abiEncoderScript.sml`
- the runtime analogue: `lowering/loweringRuntimeCorrectScript.sml`, `lowering/loweringMemCorrectScript.sml` (`external_entry_reaches_body*`) and the e2e entry theories under `lowering/e2e/`

## Notes

The statement parses: it built with `cheat` in this worktree. Many shared
ancestors are cheated locally (the commit "LOCAL OVERLAY"); that is expected.
Do not touch or revert that commit.

### Update: the non-`__init__` constructor counterexample is ruled out

The previous run's witness (`[FunctionDecl Deploy Payable F F "other" [] [] NoneT [Return NONE]]`)
was built on an old base. On the current head, `lower_vyper_deploy_unit`
(`lowering/defs/compileVyperScript.sml`) rejects a Deploy function not named
`__init__` (`ctor_named_init_def`, mirroring Python's "Only constructors can be
marked as `@deploy`!"), so `deploy_phases` fails for that program and the
witness no longer satisfies the premises. The witness theory
`ctorDeployLoweringEntryWitness` was removed. Use `compileVyperTheory.lower_vyper_deploy_unit_ctor_named_init` (used in
`ctorDeployInitcodeScript.sml` and `ctorDeployLoweringPrefixScript.sml`) to identify the
compiled constructor with the source's `__init__` lookup, and prove the frozen
statement as-is. Do not use `deploy_initcode_bounded` (admitted and false); use
`deploy_bc_size_bounded` if a deploy-code size bound is needed.
