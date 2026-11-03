# TASK: LowerDload stage: row conjuncts that need no simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: venom/compiler/o1ContractLowerDloadStageScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem lower_dload_stage_shape:
  !rpolicy view C C'.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\
    EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ ~ctx_has_dalloca C ==>
    EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\ ~ctx_has_dalloca C'

Theorem lower_dload_stage_dload_ok:
  !rpolicy view C C' vs.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    o1_ctx_shape C /\ o1_run_state_ok vs /\
    mem_inv raw_mem_ok C vs ==>
    mem_inv dload_offset_ok C' vs
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.
Do not modify any definition. Leave `lower_dload_stage_sim` and
`lower_dload_stage_mem` (cheated, out of scope) as they are. Helper lemmas go in
`venom/compiler/o1ContractLowerDloadStageScript.sml` above the frozen theorems.

## Completion Criteria

1. `holbuild -j4 build o1ContractLowerDloadStageTheory` passes, and the build log
   shows `lower_dload_stage_shape` and `lower_dload_stage_dload_ok` saved without CHEAT.
2. No `TRY`/`ORELSE` around `metis_tac` or other search; no tactic-timeout changes; no new axioms.
3. Every proof under ~50 lines; no duplicate helpers.

## Build

```
holbuild --max-heap 8000 -j4 build o1ContractLowerDloadStageTheory
```
(from the project root, the directory with holproject.toml)

## Background

LowerDload (`lower_dload_function_supply`, dispatched for `CFP_Simple VP_LowerDload`)
expands each DLOAD into ALLOCA/ADD/CODECOPY/MLOAD and each DLOADBYTES into ADD/CODECOPY
(`lower_dload_inst_supply`). It sets `fn_eom` to NONE or keeps it. `ctx_pass_stage`
relates C to C' function by function through `fn_pass_step`, keeping entry and
function names. `o1_ctx_shape` gives `fn_inst_wf` (via `o1_fn_shape`), which fixes
DLOAD's and DLOADBYTES's operand/output arity, so every one is rewritten and C' has
none; `dload_offset_ok` then holds vacuously at every instruction of C'.
`mem_inv M ctx vs` reduces to entry existence plus `M` at every `raw_reachable`
state (`mem_inv_raw_reachable`); the entry part for C' comes from C's.

## Domain Constraints

- Build only with holbuild; tactic timeout is the default 2.5 s per step.
- Never wrap search tactics in TRY/ORELSE; select goals with `>~`, `>-`, `>|`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Transform | venom/passes/lower_dload/defs/lowerDloadDefsScript.sml | `lower_dload_inst_supply`, `lower_dload_function_supply`, `dload_offset_ok` |
| Dispatcher | venom/defs/venomPassDispatcherScript.sml | `execute_configured_fn_pass_lower_dload` |
| Contract | venom/compiler/o1PassContractScript.sml | `ctx_pass_stage`, `fn_pass_step`, `o1_ctx_shape`, `o1_fn_shape` |
| Step proofs | venom/compiler/o1ContractLowerDloadScript.sml, venom/passes/lower_dload/proofs/lowerDloadSupplyProofsScript.sml | facts about the supply transform's instructions, labels, names |
| Memory invariant | venom/compiler/unitMemInvScript.sml | `mem_inv`, `mem_inv_raw_reachable`, `raw_reachable` |
| Pointer defs | venom/compiler/ptrDisciplineScript.sml | `ctx_has_dalloca` |
| Well-formedness | venom/defs/venomWfScript.sml | `fn_inst_wf`, `inst_wf` |
