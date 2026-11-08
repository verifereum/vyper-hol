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
  abiScratchDecoderArray abiDecoderCoherence abiDecoderCorrectPrimitiveArray
  abiDecoderRecursiveArray exprLowering abiDecoderContract abiEncoder abiDecoderOffsetHead
  list rich_list

Theorem calldata_scratch_dynamic_array_decoder_ptr[local]:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn P D PG.
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
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
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
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs v start src (Var root) CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
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
      start.cs_next_var limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "loop" >>
  mp_tac (SPEC_ALL calldata_scratch_array_copy_decoder_ptr) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> fs[])) >>
  disch_then ACCEPT_TAC
QED

Resume calldata_scratch_dynamic_array_decoder_ptr[loop]:
  qhdtm_assum `abi_scratch_decoder_input`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abiScratchDecoderContractTheory.abi_scratch_decoder_input_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [cj 3 type_to_abi_dec_info_def]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)
    abi_decoder_recursive_array_adds_blocks >>
  disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> disch_tac >>
  `!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)
    abi_decoder_recursive_array_code >>
  disch_then (qspec_then `func` mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  mp_tac (SPEC_ALL (SIMP_RULE bool_ss []
    (Q.INST [`bounded` |-> `T`, `final` |-> `end_st`]
      calldata_scratch_array_constructor_canonical_guarded_ptr))) >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    asm_simp_tac bool_ss [] >> decide_tac)) >>
  disch_then ACCEPT_TAC
QED

Finalise calldata_scratch_dynamic_array_decoder_ptr

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
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- suspend "base"
  >- suspend "flag"
  >- suspend "array"
  >- suspend "tuple" >>
  suspend "struct"
QED

Resume calldata_scratch_decoder_ptr[base]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bt`
  >~ [`BaseT (BytesT bound)`] >- suspend "bytes"
  >~ [`BaseT (StringT n)`] >-
    (mp_tac (SPEC_ALL (Q.INST [`ty` |-> `BaseT (StringT n)`,
       `tv` |-> `BaseTV (StringT n)`] calldata_scratch_bytestring_decoder_ptr)) >>
     (impl_tac >- asm_simp_tac bool_ss []) >> disch_then ACCEPT_TAC) >>
  irule calldata_scratch_word_decoder_ptr >>
  asm_simp_tac bool_ss [] >>
  goal_assum (drule_at (Pat `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[type_to_abi_dec_info_def, type_to_abi_clamp_def]
QED

Resume calldata_scratch_decoder_ptr[bytes]:
  Cases_on `bound`
  >- (irule calldata_scratch_word_decoder_ptr >>
      asm_simp_tac bool_ss [] >>
      goal_assum (drule_at (Pat `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[type_to_abi_dec_info_def, type_to_abi_clamp_def]) >>
  mp_tac (SPEC_ALL (Q.INST [`ty` |-> `BaseT (BytesT (Dynamic n))`,
    `tv` |-> `BaseTV (BytesT (Dynamic n))`] calldata_scratch_bytestring_decoder_ptr)) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> disch_then ACCEPT_TAC
QED

Resume calldata_scratch_decoder_ptr[flag]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule calldata_scratch_word_decoder_ptr >>
  asm_simp_tac bool_ss [] >>
  goal_assum (drule_at (Pat `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[type_to_abi_dec_info_def]
QED

Resume calldata_scratch_decoder_ptr[array]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound)` by
    fs[abi_decoder_header_def] >>
  drule abi_decoder_evaluated_array_head >> disch_tac >>
  Cases_on `bound`
  >- (mp_tac (SPEC_ALL (SIMP_RULE bool_ss []
        (Q.INST [`bounded` |-> `T`] calldata_scratch_fixed_array_decoder_guarded_ptr))) >>
      (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
        asm_simp_tac bool_ss [])) >> disch_then ACCEPT_TAC) >>
  mp_tac (SPEC_ALL (Q.INST [`maxn` |-> `n:num`]
    calldata_scratch_dynamic_array_decoder_ptr)) >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    asm_simp_tac bool_ss [])) >> disch_then ACCEPT_TAC
QED

Resume calldata_scratch_decoder_ptr[tuple]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (SIMP_RULE bool_ss []
    (Q.INST [`bounded` |-> `T`] calldata_scratch_tuple_decoder_guarded_ptr))) >>
  (impl_tac >-
    (conj_tac >- (drule LIST_REL_LENGTH >> simp[]) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_x_assum `LIST_REL _ tys tvs` mp_tac >>
         simp_tac bool_ss [LIST_REL_EVERY_ZIP, EVERY_MEM, pairTheory.FORALL_PROD] >>
         strip_tac >> first_x_assum drule >>
         disch_then (assume_tac o SIMP_RULE std_ss []) >>
         first_assum MATCH_ACCEPT_TAC) >>
     asm_simp_tac bool_ss [])) >> disch_then ACCEPT_TAC
QED

Resume calldata_scratch_decoder_ptr[struct]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (SIMP_RULE bool_ss []
    (Q.INST [`bounded` |-> `T`] calldata_scratch_struct_decoder_guarded_ptr))) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (drule LIST_REL_LENGTH >> simp[]) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_x_assum `LIST_REL _ (MAP SND args) tvs` mp_tac >>
         simp_tac bool_ss [LIST_REL_EVERY_ZIP, EVERY_MEM, pairTheory.FORALL_PROD] >>
         strip_tac >> first_x_assum drule >>
         disch_then (assume_tac o SIMP_RULE std_ss []) >>
         first_assum MATCH_ACCEPT_TAC) >>
     asm_simp_tac bool_ss [])) >> disch_then ACCEPT_TAC
QED

Finalise calldata_scratch_decoder_ptr
