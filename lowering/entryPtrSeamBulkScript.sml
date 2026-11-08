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
  calldataBulkDecoderPtr abiDecoderBulkReentry abiDecoderBulkExecute abiDecoderBulk
  abiScratchDecoderContract abiDecoderCoherence abiDecoderTypedContract
  abiScratchDecoderRanges abiDecoderCorrectPrimitiveArray abiEncoder contractABI
  abiDecoderContract abiScratchLeafEffect abiScratchEffect abiDecoderReentry abiDecoderLoop
  valueEncoding valueEncodingTyping valueEncodingProps compileEnv exprLoweringProps
  exprLowering vyperABI arithmetic normalizationPrefixPtr exprSimAggregateEncoding
  calldataTypedRobustPtr exprSimProps vyperValue vyperTyping dynarrayLiveRobustPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun venomState venomExecSemantics fragExec words list pred_set
  calldataScratchArrayConstructorPtr calldataScratchTuplePtr
  calldataScratchBytesPtr calldataScratchWordPtr decoderArrayInitPtr
  calldataDecodePtr abiScratchDecoderRecursive abiScratchDecoderArray

(* The ordinary reentry sequence and the ghost endpoint share one witness.
   Robustness uses only the count and live element strides; unused array
   capacity need not be cleared. *)
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by
    fs[abi_scratch_decoder_input_def, abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
  drule_all abi_scratch_decoder_static_array_pre >> strip_tac >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  qhdtm_assum `abi_scratch_decoder_input`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once vyper_to_abi_type_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  (qpat_assum `~is_abi_dynamic ce.ce_struct_fields ty` (fn static =>
    qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def, static])) >>
  `compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) F maxn)
    start = ((),end_st)` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
       (mp_tac o SIMP_RULE bool_ss [Once (cj 3 type_to_abi_dec_info_def)]) >>
     simp[]) >>
  drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
  drule_all abi_scratch_decoder_array_init_inputs >> strip_tac >>
  `not_fresh_at start root /\ (!x. src = Var x ==> not_fresh_at start x)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> fs[]) >>
  `lookup_var root initial = SOME (n2w d)` by fs[eval_operand_def] >>
  `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) =
     32 + maxn * type_memory_bytes ce ty` by
    simp[Once type_memory_bytes_def] >>
  `32 + LENGTH vs * type_memory_bytes ce ty <=
     type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
   d+32 < dimword (:256) /\ LENGTH vs * type_memory_bytes ce ty < dimword (:256)` by
    (qpat_x_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_scratch_decoder_ranges_def] >> strip_tac >>
     `d + (32 + maxn * type_memory_bytes ce ty) < dimword (:256)` by metis_tac[] >>
     simp[] >> irule LESS_EQ_LESS_TRANS >> qexists `maxn * type_memory_bytes ce ty` >> simp[]) >>
  drule_all calldata_bulk_decoder_endpoint_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
     start.cs_next_var limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
     b cap initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  `frag_exec ctx start end_st (\s. s = initial)
     (\t. t = actual with vs_inst_idx := LENGTH end_st.cs_current_insts) (K F)` by
    (qpat_x_assum `run_inst_seq _ initial = OK actual` mp_tac >>
     qpat_x_assum `end_st.cs_blocks = start.cs_blocks` mp_tac >>
     qpat_x_assum `end_st.cs_current_bb = start.cs_current_bb` mp_tac >>
     qpat_x_assum `isPREFIX _ _` mp_tac >>
     qpat_x_assum `EVERY _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     irule frag_exec_run_inst_seq >> fs[EVERY_CONJ]) >>
  drule abi_decode_sim_from_fragment >>
  disch_then (qspecl_then [`initial`,`func`] mp_tac) >> simp[] >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qexistsl [`actual with vs_inst_idx := LENGTH end_st.cs_current_insts`,`H`,`u`] >>
  simp[] >> (
  conj_tac >-
    (`type_memory_size tv = type_memory_bytes ce ty` by fs[abi_decoder_header_def] >>
     `EVERY (value_has_type tv) vs` by
       fs[abi_decoder_metadata_def, value_has_type_def, all_have_type_EVERY] >>
     match_mp_tac clean_live_prefix_dynarray_robust >>
     asm_simp_tac bool_ss [] >> gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]) >>

  conj_tac >- (qpat_x_assum `DISJOINT P tn.t_mem` mp_tac >>
    qpat_x_assum `u.t_mem SUBSET tn.t_mem` mp_tac >>
    rpt (pop_assum kall_tac) >> SET_TAC[]) >>
  conj_tac >- gvs[lookup_var_def] >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `abi_footprint_disjoint d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_scratch_decoder_ranges_def] >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_scratch_effect_slot >> simp[mload_def]))
QED
