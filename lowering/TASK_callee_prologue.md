# TASK: internal-call callee prologue: entry state relation

## Meta
Status: planned
Priority: P1
Created: 2026-10-26
Location: lowering/

## Theorem Statement (FROZEN)

Both theorems are in `lowering/intCallCalleeScript.sml`.

```sml
Theorem compile_internal_prologue_entry:
  !cenv params has_rb ret_type st0 cenv2 return_pc st1 func ctx args caller
   s0 f cx vs env.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) /\
    fn_has_code st0 st1 func /\ fn_inst_ids_distinct func /\
    st0.cs_current_insts = [] /\
    st0.cs_current_bb = (HD func.fn_blocks).bb_label /\
    setup_callee func args caller = SOME s0 /\
    state_rel f cenv cx (vs with scopes := []) caller /\
    internal_args_rel cenv params env (if has_rb then 1 else 0) args
      caller.vs_alloca_next caller.vs_memory /\
    caller.vs_alloca_next + internal_stack_size cenv params
      < dimword (:256) ==>
    ?s1.
      ~s1.vs_halted /\ s1.vs_current_bb = st1.cs_current_bb /\
      s1.vs_inst_idx = LENGTH st1.cs_current_insts /\
      stmt_state_rel func (cenv2 with ce_alloca_locals := T) cx
        (vs with scopes := [env]) s1 /\
      fresh_vars_wrt st1 s1 /\
      (?x. return_pc = Var x /\ not_fresh_at st1 x /\
           lookup_var x s1 = SOME s0.vs_return_pc_token) /\
      (has_rb ==>
       ?rb. not_fresh_at st1 rb /\ lookup_var rb s1 = SOME (HD args) /\
            !off sz. cenv.ce_return_buf = SOME (MemLoc off sz) ==>
                     cenv2.ce_return_buf = SOME (PtrVar (Var rb) sz)) /\
      !fuel r. run_from fuel ctx func s1 = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx func s0 = r

Theorem compile_internal_prologue_code:
  !cenv params has_rb ret_type st0 cenv2 return_pc st1.
    compile_internal_prologue cenv params has_rb ret_type st0 =
      ((cenv2, return_pc), st1) /\
    ALL_DISTINCT (MAP FST params) /\
    (!i. i < LENGTH params ==>
         ?off sz. FLOOKUP cenv.ce_vars (FST (EL i params)) =
                  SOME (MemLoc off sz)) /\
    (!n off sz. FLOOKUP cenv.ce_vars n = SOME (MemLoc off sz) ==>
                MEM n (MAP FST params)) /\
    (!n p sz. FLOOKUP cenv.ce_vars n <> SOME (PtrVar p sz)) ==>
    st1.cs_blocks = st0.cs_blocks /\
    st1.cs_current_bb = st0.cs_current_bb /\
    isPREFIX st0.cs_current_insts st1.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st0 st1) /\
    ~block_is_terminated st1 /\
    local_ptrs_reserved (cenv2 with ce_alloca_locals := T) st1
```

The definitions `compile_internal_prologue`, `internal_stack_size` and
`internal_args_rel` are in the same file, above the theorems; do not change
them either.

**Do not modify these statements.** Prove them as-is, or produce a
counterexample.

`materialize_internal_params_run` in the same file is weakly frozen: it is
the intended statement of the materialization step, and you may strengthen
or adjust its hypotheses and conclusion if the proof needs it, as long as
the two frozen theorems stay as they are.

## Completion Criteria

1. `holbuild -j4 build intCallCalleeTheory` passes with zero CHEAT warnings
   and zero failures.
2. `holbuild -j4 build vyperLoweringHolTheory` passes.
3. No duplicate or near-duplicate lemmas: reuse the lemmas listed below
   rather than restating them.

**If a theorem is false as stated:**
- Produce a HOL4 counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <worktree root, the directory with holproject.toml>
holbuild -j4 build intCallCalleeTheory
```

## Background

vyper-hol proves that its Vyper-to-Venom lowering is correct. An internal
call compiles to an `INVOKE`; the callee (`compile_internal_function`,
`lowering/defs/moduleLoweringScript.sml`) starts with a prologue: `PARAM`s
for the return buffer and the arguments, `RETPC_PARAM`, then
`materialize_internal_params`, which gives each stack-passed argument an
`ALLOCA` region and stores it there, and records memory-passed ones at
their argument pointer, and then a temporary return-value `ALLOCA`.
`compile_internal_prologue` is that prefix, and
`compile_internal_function_prologue` (proved) splits
`compile_internal_function` at it.

The entry theorem says that running the prologue from the state
`setup_callee` builds reaches the start of the body in a state related to
the source's callee state (scope `env`) by `stmt_state_rel`, the relation
the statement lemmas take. The code theorem gives the compile-side facts
the statement lemmas need at the body's start.

## Domain Constraints

- No `cheat`, no new axioms, no `TRY`/`ORELSE` around search tactics
  (`metis_tac`, `simp`, `fs`, `gvs`, ...), no raising the 2.5 s tactic
  timeout.
- Don't edit files outside `lowering/intCallCalleeScript.sml` except to add
  a genuinely general lemma to the theory where its subject lives; then
  build that theory and its dependents.
- holbuild is the build tool; Holmake isn't used.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| The task's theory | `lowering/intCallCalleeScript.sml` | prologue def, hypotheses' defs, proved shape and step lemmas |
| Repo conventions | `AGENTS.md` | proof style, build rules |
| Compile env, relations | `lowering/defs/compileEnvScript.sml` | `state_rel`, `local_ptrs_rel`, `local_region`, `local_backed`, `local_ptrs_reserved`, `fresh_vars_wrt`, `not_fresh_at`, `regions_disjoint`, compile monad |
| The prologue's source | `lowering/defs/moduleLoweringScript.sml` | `compile_internal_param_decls`, `materialize_internal_params`, `compile_internal_function` |
| Emit helpers | `lowering/defs/emitHelperScript.sml`, `lowering/defs/contextScript.sml` | `emit_op`, `emit_void`, `compile_alloc_buffer` |
| Venom semantics | `venom/defs/venomExecSemanticsScript.sml` | `step_inst_base` (PARAM, RETPC_PARAM, ALLOCA, MSTORE), `exec_alloca`, `setup_callee`, `run_from` |
| Fragment execution | `lowering/fragExecScript.sml` | `fn_has_code`, `fn_has_code_same_block`, `frag_exec_run_inst_seq`, `lookup_block_fn_insts` |
| Local pointer lemmas | `lowering/localPtrsPropsScript.sml` | `local_ptrs_rel_exec_alloca(_fresh)`, `local_ptrs_rel_mstore`, `local_ptrs_rel_frame`, `local_ptrs_rel_fresh_not_local_ptr`, `alloca_inv_exec_alloca`, `alloca_inv_fields`, `fn_inst_ids_distinct_inj`, `mstore_keeps_val_in_memory` |
| Expression lowering props | `lowering/exprLoweringPropsScript.sml` | `run_inst_seq`, `emitted_insts`, `stmt_state_rel`, `state_rel_frame`, `stmt_state_rel_inst_idx` |
| Halting/alloca helpers | `lowering/loweringHaltScript.sml` | `step_alloca_fresh`, `step_alloca_fresh_inv`, `compile_alloc_buffer_insts` |
| Value encoding | `lowering/valueEncodingPropsScript.sml` | `mstore_mem_word_at_same`, `val_in_memory_mem_agree` |
| Indexed lists | HOL `indexedListsTheory` | `findi`, `findi_EL`, `EL_findi` |
