# TASK: S3 entry seam: pointer-safe bulk-copy dynamic-array decoder

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: lowering/entryPtrSeamBulkScript.sml

## Theorem Statement (FROZEN)

1 theorem, currently `cheat` in `lowering/entryPtrSeamBulkScript.sml`. Prove it. Copy of the statement as it stands in the source:

```sml
Theorem calldata_scratch_array_copy_decoder_ptr:
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) start =
    ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src (Var root)
    CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ lower <= initial.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?actual H u.
    val_in_memory (ArrayTV tv (Dynamic maxn)) v d actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) v d mem) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
      start.cs_next_var limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial
      actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    ptr_covers H u root actual (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
```

**Do not modify this statement. Prove it as-is, or produce a counterexample.**

## Completion Criteria

1. `holbuild -j4 build entryPtrSeamBulkTheory` passes with `calldata_scratch_array_copy_decoder_ptr` proved: no `cheat` in `lowering/entryPtrSeamBulkScript.sml` nor in any theory this run adds, and no FAILs.
2. Nothing in `lowering/loweringPtrCorrectScript.sml` or the other `lowering/entryPtrSeam*Script.sml` files changes.
3. No duplicate or near-duplicate lemmas; helpers in their most general form.

**If the theorem is false as stated:**
- Produce a counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build entryPtrSeamBulkTheory
```

Run from the project root (the directory holding `holproject.toml` and this file).

## Background

S3 says the lowered Vyper unit's raw Venom run satisfies the pointer discipline and keeps taint within the source call's dead bytes. Its entry theorem `external_entry_reaches_body_ptr` (in `lowering/loweringPtrCorrectScript.sml`) is now proved from five seams, each its own theory with one `cheat`ed theorem: `entryPtrSeamDead` (the body's dead bytes are the call's), `entryPtrSeamPrefix` (selector dispatch and passing entry checks), `entryPtrSeamRegister` (argument registration reaches the body's start with the S1 relation and the ghost), `entryPtrSeamDecoder` (the pointer-safe calldata decoder contract for every coherent type) and `entryPtrSeamBulk` (its bulk-copy dynamic-array case). This task proves one of them.

A pointer-safe run (`ptr_safe_run`/`ptr_safe_blocks`, `venom/compiler/ptrSafeRunScript.sml`) checks each executed instruction against `ptr_inst_ok` while threading a ghost: provenance `G` (pointer variable -> base, size) and taint `tn` (tainted variables and memory, storage, transient bytes). The judgments in `lowering/bodyPtrDefsScript.sml` (`ptr_covers`, `ghost_inv`, `mem_agree_outside`, `cx_dead`, ...) are the pointer twins of S1's. The selector dispatch and the entry checks touch no memory; the argument decode writes only the parameters' buffers (ALLOCAs whose provenance the ghost records), from calldata, so untainted.

This seam: A calldata dynamic array whose elements are static and need no clamp is decoded by a count guard, an MSTORE of the count, and one CALLDATACOPY (`can_bulk_copy` in `compile_abi_decode_to_buf`). The seam is the pointer-safe decoder contract for that shape: the contract the lane proved for the other decoder shapes (`lowering/calldataScratch{Word,Bytes,Tuple}PtrScript.sml`, `lowering/calldataScratchArrayConstructorPtrScript.sml`), one witness for the ordinary endpoint and the ghost. Its ordinary half is `abi_scratch_decoder_array_copy` (`lowering/abiScratchDecoderArrayScript.sml`).

## Domain Constraints

- Build with holbuild only (no Holmake). The tactic timeout is the project default, 2.5 s per step; don't raise it, and pass no timeout flags.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Don't edit proven statements in other theories, and don't change any definition (in particular nothing in `lowering/defs/`, `venom/`, `lowering/bodyPtrDefsScript.sml`, `lowering/bodyMemoryDefs*`). Don't add axioms or new `cheat`s. No `let` in theorem statements.
- Leave `lowering/loweringPtrCorrectScript.sml` alone: its theorems (`external_entry_reaches_body_ptr`, `external_entry_value_revert_ptr`, `external_frame_ret_ok_ptr`, `body_stmts_sim_ptr` and the rest) are not this task's; don't prove, restate or edit them. Don't edit the other `entryPtrSeam*Script.sml` files either.
- New helper lemmas go in new theories under `lowering/` named for what they prove, or in this seam's own theory file. A new theory must be an ancestor of this seam's theory so its build reaches it. You may use and extend the lane's proved helper theories (`lowering/*PtrScript.sml` and their ancestors); a restated variant of one of them gets a new name, its original stays.
- The named admissions already in the tree may be used as given: S1's in `lowering/loweringRuntimeCorrectScript.sml`, and nothing else (this seam needs no admission). Don't prove, restate or weaken them.
- Commit only proof sources (no task/state/plan/log files). Commit trailer: `Bot: opus (Claude Opus 5.5)`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| this seam | lowering/entryPtrSeamBulkScript.sml | the frozen statement, with hints as comments above it |
| the composer | lowering/loweringPtrCorrectScript.sml | how `external_entry_reaches_body_ptr` consumes the seams (read only) |
| ptr judgments | lowering/bodyPtrDefsScript.sml | cx_dead, mem_agree_outside, ptr_covers, return_buf_ptr, stor_taint_ok, ghost_inv |
| pointer-safe runs | venom/compiler/ptrSafeRunScript.sml | ptr_inst_ok, ptr_safe_run/blocks, ghost_run, fuel lemmas |
| pointer discipline | venom/compiler/ptrDisciplineScript.sml | access_ok, taint_ok, step_prov/step_taint, entry_taint, allocas_from, ctx_has_dalloca |
| decoder contracts | lowering/calldataScratch*PtrScript.sml, lowering/decoderArrayInitPtrScript.sml, lowering/calldataDecodePtrScript.sml | the other shapes, count guard and header endpoints, calldata-copy boundary |
| ordinary decoder | lowering/abiScratchDecoderArrayScript.sml, lowering/abiScratchDecoderContractScript.sml, lowering/abiScratchEncoderContractScript.sml | abi_scratch_decoder_array_copy, abi_scratch_decoder_input, abi_scratch_effect |
| decoder code | lowering/defs/abiEncoderScript.sml | compile_abi_decode_to_buf |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml, venom/defs/venomStateScript.sml | step_inst, run_from, state |

## Notes

- Hints for this seam are SML comments above its statement; they are not binding.
- Build with `-j4` at most; never `holbuild run`/`repl`.
