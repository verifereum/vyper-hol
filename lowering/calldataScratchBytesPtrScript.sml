(* Original-state bytes/string scratch decoder ghost contract. *)
Theory calldataScratchBytesPtr
Ancestors calldataScratchWordPtr calldataDecodePtr abiValidBytesReentry abiDecoderBytes
  abiDecoderValidBytesInput abiScratchDecoderRanges abiDecoderBytesFrame abiDecoderBytesTyped
  calldataTypedRobustPtr loweringPosts exprSimDefs exprSimProps abiDecoderLoop abiScratchEncoderContract
  abiDecoderValidBytes abiDecoderReentryPointer abiScratchLeafEffect
  abiDecoderReentry abiDecoderContract abiDecoderTypedContract
  abiScratchDecoderContract abiScratchEffect valueEncodingTyping valueEncodingProps
  ctorAbiActualAlloc exprLowering exprLoweringProps emitHelper rich_list venomInst fragExec
  bodyPtrDefs ptrDiscipline valueEncoding compileEnv venomExecSemantics
  venomState words pred_set arithmetic list

(* The calldata instance of trunk's position-form decoder lemmas: the source
   base operand is Lit 0w and the numeric base is 0. *)
val calldata_pos_live_lit = prove(
  ``!n w. abiDecoderReentry$abi_decoder_operand_live n (Lit w)``,
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def]);
fun calldata_pos th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES, calldata_pos_live_lit]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem calldata_scratch_bytestring_decoder_ptr:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
    CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d first last b cap initial /\
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
  drule_all (calldata_pos abi_scratch_decoder_input_point) >> strip_tac >>
  drule_all (calldata_pos abi_decoder_valid_bytes_input) >> strip_tac >>
  `compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring n) start = ((),end_st)` by metis_tac[] >>
  drule_all (calldata_pos abi_decoder_valid_bytes_reentry) >> strip_tac >>
  drule (calldata_pos abi_decoder_valid_bytes_facts) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n < dimword (:256) /\ LENGTH payload <= n /\
   eval_operand src initial = SOME (n2w sb) /\
   eval_operand (Var root) initial = SOME (n2w d)` by
    (qpat_x_assum `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_scratch_decoder_input_def, abi_scratch_decoder_ranges_def,
       abi_decoder_valid_bytes_pre_def] >> metis_tac[]) >>
  `not_fresh_at start root /\ (!q. src = Var q ==> not_fresh_at start q)` by
    (qpat_x_assum `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_scratch_decoder_input_def, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> simp[]) >>
  `abi_decode_load CALLDATALOAD (n2w sb:bytes32) initial = n2w (LENGTH payload)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >>
     simp[abi_decode_load_def]) >>
  `ptr_covers G tn root initial (abi_decode_bytes_copy_size n)` by metis_tac[] >>
  `abi_decode_bytes_copy_size n = 32 + 32 * ((n + 31) DIV 32)` by
    simp[abi_decode_bytes_copy_size_def] >>
  drule_all calldata_bytestring_overwrite_prefix >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `val_in_memory tv v d actual.vs_memory` by metis_tac[] >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
    start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual` by
    (qpat_x_assum `abi_decoder_budget _ _ _ _ _` mp_tac >>
     qpat_x_assum `fresh_vars_wrt limit_st actual` mp_tac >>
     qpat_x_assum `actual.vs_allocas = _` mp_tac >>
     qpat_x_assum `actual.vs_alloca_next = _` mp_tac >>
     qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
     qpat_x_assum `actual.vs_halted = _` mp_tac >>
     qpat_x_assum `!op w. _` mp_tac >>
     qpat_x_assum `type_memory_bytes ce ty = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial` by
    (rpt strip_tac >> irule ctor_actual_sequence_var_frame >>
     qexists `emitted_insts start end_st` >> simp[] >>
     drule calldata_bytestring_decoder_instructions >> strip_tac >>
     qpat_x_assum `not_fresh_at start x` mp_tac >>
     qpat_x_assum `end_st.cs_current_insts = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
       not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  qexistsl [`actual with vs_inst_idx := LENGTH end_st.cs_current_insts`,`G'`,`tn'`] >>
  simp[] >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "execution" >>
  conj_tac >- suspend "coverage" >>
  conj_tac >- (qpat_x_assum `DISJOINT P tn.t_mem` mp_tac >>
    qpat_x_assum `tn'.t_mem SUBSET tn.t_mem` mp_tac >>
    rpt (pop_assum kall_tac) >> SET_TAC[]) >>
  conj_tac >- suspend "variables" >>
  conj_tac >- (fs[allocas_from_def] >> metis_tac[]) >>
  suspend "slots"
QED

Resume calldata_scratch_bytestring_decoder_ptr[robust]:
  rpt strip_tac >>
  `value_has_type tv v` by fs[abi_scratch_decoder_input_def, abi_decoder_metadata_def] >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  `val_footprint tv v <= type_memory_bytes ce ty` by
    (irule LESS_EQ_TRANS >> qexists `type_memory_size tv` >>
     simp[val_footprint_le] >> fs[abi_scratch_decoder_input_def, abi_decoder_metadata_def]) >>
  irule clean_footprint_val_in_memory_robust >> simp[] >>
  qexistsl [`actual.vs_memory`,`tn'.t_mem`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac
QED

Resume calldata_scratch_bytestring_decoder_ptr[execution]:
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all (calldata_pos abi_decoder_bytes_shape) >> strip_tac >>
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

Resume calldata_scratch_bytestring_decoder_ptr[coverage]:
  gvs[]
QED

Resume calldata_scratch_bytestring_decoder_ptr[variables]:
  gvs[lookup_var_def]
QED

Resume calldata_scratch_bytestring_decoder_ptr[slots]:
  rpt strip_tac >>
  `abi_footprint_disjoint d (type_memory_bytes ce ty)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_scratch_decoder_input_def, abi_scratch_decoder_ranges_def] >>
  drule_all abi_scratch_effect_slot >> simp[mload_def]
QED

Finalise calldata_scratch_bytestring_decoder_ptr
