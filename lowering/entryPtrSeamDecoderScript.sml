(*
 * Seam of external_entry_reaches_body_ptr (loweringPtrCorrect): the
 * pointer-safe calldata decoder contract for every type the ordinary
 * decoder handles (abi_decoder_coherent), the pointer twin of
 * abiScratchDecoderRecursive's abi_scratch_decoder_coherent_correct.
 *
 * The contract is calldataScratch*Ptr's: one witness `actual` for both the
 * ordinary endpoint (val_in_memory, abi_scratch_effect, abi_decode_sim) and
 * the ghost (H, u) there, the decoded value robust to the bytes u taints,
 * and the all-fuel safety continuation back to `initial`.  It carries
 * lower <= initial.vs_alloca_next: a dynamic array decoded by its element
 * loop allocates its index slot at vs_alloca_next, so without it
 * allocas_from lower actual can fail.
 *)
Theory entryPtrSeamDecoder
Ancestors
  entryPtrSeamBulk calldataScratchArrayConstructorPtr calldataScratchTuplePtr
  calldataScratchBytesPtr calldataScratchWordPtr abiScratchDecoderRecursive
  abiScratchDecoderArray abiDecoderCoherence

(* SEAM (cheated; proved by its own alan run).
   Hints (not binding):
   - Shape: induction on abi_decoder_coherent_ind, as
     abi_scratch_decoder_coherent_correct does; the cases have pointer
     lemmas already: calldata_scratch_word_decoder_ptr,
     calldata_scratch_bytestring_decoder_ptr, calldata_scratch_tuple_decoder_ptr,
     calldata_scratch_fixed_array_decoder_ptr, calldata_scratch_struct_decoder_ptr,
     calldata_scratch_array_constructor_canonical_ptr (element loop) and the
     sibling seam calldata_scratch_array_copy_decoder_ptr (bulk copy).
   - Gap: the child hypotheses of the tuple/fixed-array/struct lemmas and of
     the array constructor lemmas quantify over every `lower` without
     lower <= initial.vs_alloca_next, which a loop-decoded dynamic-array
     child cannot meet.  Expect to restate them (new names, proofs reused)
     with the child contract at the parent's own `lower` and that premise,
     carried to each child by vs_alloca_next only growing.
   - The loop case's extra side conditions (no PHI at the loop exit block,
     the nonzero-length element array condition, the
     abi_decode_array_loop_init / compile_abi_decode_dyn_loop split of
     compile_abi_decode_to_buf) are discharged in the ordinary
     abi_scratch_decoder_array_loop / abi_scratch_decoder_evaluated_array. *)
Theorem calldata_scratch_decoder_ptr:
  !ce env sf ty tv.
    abi_decoder_coherent ce env sf ty tv ==>
    !start end_st func ctx src root bs v sb d first last b cap limit_st initial
     G tn lower P D PG.
      compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
        (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
      fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
      (start.cs_blocks = end_st.cs_blocks \/
        !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
      abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
        CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
      abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
      end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
      fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
      initial.vs_current_bb = start.cs_current_bb /\
      initial.vs_inst_idx = LENGTH start.cs_current_insts /\
      ptr_covers G tn root initial (type_memory_bytes ce ty) /\
      op_taint tn src = {} /\ op_prov G src = NONE /\
      allocas_from lower initial /\ lower <= initial.vs_alloca_next /\
      ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
      ?actual H u.
        val_in_memory tv v d actual.vs_memory /\
        (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
          val_in_memory tv v d mem) /\
        abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
          start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial
          actual /\
        actual.vs_current_bb = end_st.cs_current_bb /\
        actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
        abi_decode_sim ctx func initial actual /\
        ptr_covers H u root actual (type_memory_bytes ce ty) /\
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
