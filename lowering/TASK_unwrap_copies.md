# TASK: Prove unwrap_value's storage and runtime-code aggregate copies

## Meta
Status: planned
Priority: P1
Created: 2026-11-01
Location: lowering/ (vyper-hol, theory exprSimCopy)

## Theorem Statement (FROZEN)

Two theorems in `lowering/exprSimCopyScript.sml`:

```sml
Theorem unwrap_storage_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R

Theorem unwrap_runtime_code_copy_sim:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op R.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) ==>
    frag_exec ctx sm sb
      (\s. vv_post ctx func cenv cx e es sa sm s0 es' (Value v)
             (LocatedValue t p) s)
      (\s. expr_post ctx func cenv cx e es sa sb s0 es' v op s) R
```

Key definitions: `unwrap_value_def` (lowering/defs/exprLoweringScript.sml),
`compile_ensure_in_memory_def`, `compile_word_copy_loop_def`,
`compile_imm_copy_to_memory_def`, `compile_alloc_buffer_def`
(lowering/defs/contextScript.sml, emitHelper), `vv_post_def`, `vv_holds_def`,
`storage_holds_def`, `immutable_holds_def`, `sub_layout_def`,
`expr_post_def`, `expr_val_at_def` (lowering/exprSimScript.sml),
`frag_exec_def` (lowering/fragExecScript.sml).

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

The third theorem in the file, `unwrap_ctor_code_copy_sim`, is out of scope:
leave its cheat and comment untouched.

## Completion Criteria

1. `exprSimCopyTheory` builds with zero CHEAT warnings for the two theorems
   above (the third keeps its cheat).
2. `exprSimUnwrapTheory` still builds (it consumes the two theorems).
3. If you move existing lemmas into or below exprSimCopy (see Domain
   Constraints), update every reference to them (grep for their names).
   Theories above exprSimUnwrap are being repaired on another branch at
   the same time, so don't build them; they're checked when the branches
   are merged.
4. No duplicate or near-duplicate lemmas.

**If a theorem is false as stated:** produce the counterexample and the
tightest sufficient fix. Do NOT silently weaken the statement.

## Build

```
cd <worktree root, the directory with holproject.toml>
timeout 3600 holbuild --max-heap 7000 -j4 build exprSimCopyTheory exprSimUnwrapTheory
```

## Background

vyper-hol proves Vyper→Venom lowering correct by an expression simulation.
`unwrap_value` turns a compiled value into an operand; for an aggregate
held in storage, transient storage or (at runtime) the code's data section,
it allocates a memory buffer (`ALLOCA` of `type_memory_bytes cenv t` bytes)
and copies the value's words into it. `vv_post` says the source location
holds the value; `expr_post` says the result operand points at a buffer of
this expression's own holding it (`expr_val_at`), plus the frame conditions
(variables, allocas, older memory, locals kept). These two theorems are the
last unproved steps of `unwrap_copy_sim` in `exprSimUnwrapScript.sml`.

## Domain Constraints

- holbuild only (no Holmake, no hol4-mcp, no REPL sessions).
- Never change or raise the tactic timeout; a slow step is a bug in the
  proof: split it.
- No `TRY`/`ORELSE` around `metis_tac` or any search tactic; select goals
  with `>~`, `>-`, `>|`.
- No `cheat` in the result, no new axioms, no changed statement of any
  existing theorem used by other theories.
- `exprSimBuffer`, `exprSimLiteralBuffer` and `exprSimHyps` are above
  exprSimCopy in the theory graph (they import exprSimUnwrap), so they
  can't be imported. You may move an existing lemma from them into
  exprSimCopy (or a theory below it) with its statement unchanged, then
  delete the original and fix the references (e.g.
  `exprSimLiteralBufferTheory.literal_emit_mstore_run` is referenced
  qualified in exprSimAggregateLoopsScript.sml).
- Don't edit `bodyStoragePreservation*` or `exprStoragePreservation*`.
- Theory headers use `Theory`/`Ancestors`/`Libs`; no `new_theory`/`store_thm`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| one-word versions (proved) | lowering/exprSimUnwrapScript.sml | `unwrap_storage_word_sim`, `storage_word_load`, `storage_holds_load`, `unwrap_runtime_immutable_word_sim`, `immutable_holds_dload`, `step_DLOAD`, `expr_post_of_vv_post_load` |
| storage copy loop (runs, contents not proved) | lowering/exprSimStorageCopyScript.sml | `compile_storage_copy_defined_frag`, `ensure_storage_memory_layout`, `storage_copy_alloc_layout`, many `[local]` loop/step lemmas you may un-local or generalise |
| buffer post frame | lowering/exprSimBufferScript.sml | `buffer_memory_vv_post_general`, `buffer_alloc_code` |
| alloca/mstore runs | lowering/exprSimLiteralBufferScript.sml | `literal_alloc_buffer_run`, `literal_alloca_run`, `literal_mstore_state_rel`, `literal_emit_mstore_run`, `alloc_buffer_frame_run` |
| immutable copy execution | lowering/proofs/immutableCopyExecutionScript.sml | `immutable_copy_suc`, `immutable_transfer_one_execution`, frame lemmas for `compile_imm_copy_to_memory` |
| state relation | lowering/defs/compileEnvScript.sml | `storage_agree`, `storage_read_live`, `immutables_rel`, `state_rel` |
| stmt_state_rel facts | lowering/loweringSliceScript.sml | `stmt_state_rel_exec_alloca`, `immutables_rel_mstore_alloca` |
| local pointers | lowering/localPtrsPropsScript.sml | `local_ptrs_rel_mstore`, `local_ptrs_rel_alloca_disjoint` |
| storage decoding | semantics/vyperStorageScript.sml, semantics/prop/vyperLookupStorageScript.sml | `read_storage_slot`, `decode_value`, `slots_in_range`, `word_slot_canonical` |
| typing of decoded values | semantics/prop/vyperTypeStatePreservationScript.sml, lowering/valueEncodingTypingScript.sml | `decode_value_well_typed`, `value_has_type_val_wf` |
| memory encoding | lowering/defs/valueEncodingScript.sml | `type_memory_size`, `val_in_memory`, `val_wf` |
| frag_exec rules | lowering/fragExecScript.sml | `frag_exec_seq`, `frag_exec_conseq`, `frag_exec_loop`, `frag_exec_run_inst_seq`, `fn_has_code_split` |
| repo conventions | AGENTS.md | proof style rules for this repo |

## Notes

- A previous run found that without the `not_fresh_at sm` premise on the
  pointer operand the storage statement is false: the buffer's ALLOCA can
  write the pointer's own variable. That premise is now in both statements
  (its evidence, `unwrapCopyProbeTheory`, is on branch
  `bot/opus/seq-479-copy-alan`); callers discharge it with
  `exprOperandVarTheory.compiler_compile_var`.

- `vv_holds` forces the value_vv's type to be `expr_type e`, so `t =
  expr_type e` under the precondition.
- Storage word layout matches memory word layout: slot i of the value is
  memory word i of the buffer (`type_memory_size = 32 * type_slot_size`).
  Dead bytes past a bytestring's or dynarray's length aren't related by
  `storage_agree`, but `val_in_memory` doesn't read them either.
