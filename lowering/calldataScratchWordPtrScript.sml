(* Full original-state scratch decoder contract for primitive words. *)
Theory calldataScratchWordPtr
Ancestors calldataTypedRobustPtr abiScratchDecoderTuple abiScratchLeafEffect
  representationCleanPtr abiScratchEffect decoderGhostFramePtr ptrDiscipline
  abiDecoderPrimitiveCaller abiDecoderReentry abiDecoderLayout abiDecoderContract
  abiScratchDecoderContract abiScratchEncoderContract venomExecSemantics
  compileEnv valueEncoding venomState words pred_set arithmetic
  ctorAbiActualAlloc abiDecoderClampedWord exprLowering emitHelper rich_list
  abiEncoder fragExec venomInst exprLoweringProps valueEncodingTyping
  valueEncodingProps abiDecoderTypedContract abiDecoderReentry bodyPtrDefs loweringPosts exprSimDefs exprSimProps
  abiDecoderLoop list

Theorem calldata_scratch_word_decoder_ptr:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
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
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
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
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_word_pre >> strip_tac >>
  drule abi_decoder_primitive_source >> strip_tac >>
  `compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
    (DecPrimWord clamp) start = ((),end_st)` by metis_tac[] >>
  `ptr_covers G tn root initial 32` by metis_tac[] >>
  drule_all calldata_primitive_reentry_ptr_endpoint >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` kall_tac >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
    start.cs_next_var limit_st d 32 b cap initial actual` by
    (irule abi_scratch_leaf_effect >> simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial` by
    (rpt strip_tac >> irule ctor_actual_sequence_var_frame >>
     qexists `emitted_insts start end_st` >> simp[] >>
     qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ (DecPrimWord _) _ = _` mp_tac >>
     qpat_x_assum `not_fresh_at start x` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `clamp` >>
     FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
     simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     gvs[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  qexistsl [`endpoint`,`G'`,`tn'`] >> simp[] >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "execution" >>
  conj_tac >- suspend "coverage" >>
  conj_tac >- (qpat_x_assum `DISJOINT P tn.t_mem` mp_tac >>
    qpat_x_assum `tn'.t_mem SUBSET tn.t_mem` mp_tac >>
    rpt (pop_assum kall_tac) >> SET_TAC[]) >>
  conj_tac >- (gvs[lookup_var_def]) >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  suspend "slots"
QED

Resume calldata_scratch_word_decoder_ptr[robust]:
  rpt strip_tac >>
  `value_has_type tv v` by fs[abi_decoder_metadata_def] >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `val_footprint tv v <= 32` by
    (irule LESS_EQ_TRANS >> qexists `type_memory_size tv` >>
     simp[val_footprint_le] >> fs[abi_decoder_metadata_def]) >>
  irule clean_footprint_val_in_memory_robust >> simp[] >>
  qexistsl [`actual.vs_memory`,`tn'.t_mem`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Resume calldata_scratch_word_decoder_ptr[execution]:
  rpt strip_tac >> gvs[] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
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
  disch_then (qspecl_then [`initial`,`func`] mp_tac) >> simp[]
QED

Resume calldata_scratch_word_decoder_ptr[coverage]:
  gvs[]
QED

Resume calldata_scratch_word_decoder_ptr[slots]:
  rpt strip_tac >>
  `abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_scratch_decoder_input_def, abi_scratch_decoder_ranges_def] >>
  drule_all abi_scratch_effect_slot >>
  simp[mload_def]
QED

Finalise calldata_scratch_word_decoder_ptr
