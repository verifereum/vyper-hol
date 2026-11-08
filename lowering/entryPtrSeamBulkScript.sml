(*
 * Seam of external_entry_reaches_body_ptr (loweringPtrCorrect): the
 * pointer-safe decoder contract for a calldata dynamic array whose elements
 * are static and need no clamp, which compile_abi_decode_to_buf decodes by
 * a bulk CALLDATACOPY (can_bulk_copy) instead of the element loop.
 *
 * The contract is the one calldataScratch{Word,Bytes,Tuple}Ptr and
 * calldataScratchArrayConstructorPtr prove for the other decoder shapes
 * (same witness for the ordinary endpoint and the ghost), with
 * lower <= initial.vs_alloca_next among its premises as in
 * calldata_scratch_array_constructor_canonical_ptr.  Its ordinary half is
 * abiScratchDecoderArray's abi_scratch_decoder_array_copy.
 *)
Theory entryPtrSeamBulk
Ancestors
  calldataScratchArrayConstructorPtr calldataScratchTuplePtr
  calldataScratchBytesPtr calldataScratchWordPtr decoderArrayInitPtr
  calldataDecodePtr abiScratchDecoderRecursive abiScratchDecoderArray

(* SEAM (cheated; proved by its own alan run).
   Hints (not binding): the code is the count guard and header shared with
   the loop path (decoderArrayInitPtr's count-guard and header endpoints),
   then MSTORE of the count at dst and one CALLDATACOPY of cnt * elem_mem_sz
   bytes to dst + 32 (calldataDecodePtr's calldata-copy boundary); the
   ordinary half is abi_scratch_decoder_array_copy. *)
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
Proof
  cheat
QED
