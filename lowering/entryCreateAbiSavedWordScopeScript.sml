Theory entryCreateAbiSavedWordScope
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  abiEncodeValuesWordRow abiEncodeValuesCode bodyFullExtCallDirectWord
  placeMemoryCodeLayout emitHelperProps abiEncoderProps
  loweringShapeRules
  abiEncoderWindowPhase abiEncoderWindowSequence exprLoweringProps
  exprLowering context compileEnv venomState venomInst words list finite_map
  pred_set arithmetic pair

Theorem compile_word_store_emit[local]:
  is_word_type ty /\
  compile_store_memory ce src (Var p) ty ty st = ((),en) ==>
  emit_void MSTORE [Var p;src] st = ((),en)
Proof
  strip_tac >> gvs[compile_store_memory_def]
QED
Theorem emit_void_current_bb[local]:
  emit_void opc ops st = ((),st') ==> st'.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >> drule emit_void_same_blocks >> simp[same_blocks_def]
QED

Theorem create_abi_saved_word_row_confined:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_value_rows ce (Var dst) cursor h
    [(StackValue tag src,ty)] su = ((),en) /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset)
    cursor loc slot i su u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\
  LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand src u = SOME (typed_val_to_w256 tv v) /\ op_taint tu src = {} /\
  (!x. src = Var x ==> not_fresh_at su x) /\ fn_has_code su en func ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset)
      cursor loc slot (SUC i) en z Gz tz /\
    (?raw. run_inst_seq (emitted_insts su en) u = OK raw /\
           z = raw with vs_inst_idx := LENGTH en.cs_current_insts) /\
    create_expr_prefix su en explicit ctx func u [] z /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule bodyFullExtCallDirectStateTheory.abi_encode_saved_state_resources >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule_all abi_encode_saved_word_row_pure_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac)) >>
  `~is_abi_dynamic ce.ce_struct_fields ty` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  drule_all abi_encode_value_rows_static_trace >>
  disch_then (qx_choose_then `head` (qx_choose_then `prepared`
    strip_assume_tac)) >>
  gvs[unwrap_value_def, compile_abi_encode_value_rows_def, comp_return_def] >>
  `head = Var (STRING #"%" (toString su.cs_next_var))` by
    (qpat_assum `emit_op ADD _ su = _` (fn th =>
       mp_tac (MATCH_MP placeMemoryCodeLayoutTheory.emit_op_next_var th) >>
       simp[])) >>
  qpat_x_assum `head = _` SUBST_ALL_TAC >>
  drule_all compile_word_store_emit >> disch_then assume_tac >>
  `en.cs_current_bb = su.cs_current_bb` by
    (drule emit_void_current_bb >>
     qpat_assum `emit_op ADD _ su = _` (fn th =>
       mp_tac (MATCH_MP emit_op_facts th)) >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `prepared.cs_current_insts = su.cs_current_insts ++
      emitted_insts su prepared` by simp[] >>
  `en.cs_current_insts = prepared.cs_current_insts ++
      emitted_insts prepared en` by simp[] >>
  `emitted_insts su en = emitted_insts su prepared ++
      emitted_insts prepared en` by metis_tac[emitted_insts_append] >>
  `en.cs_current_insts = su.cs_current_insts ++
      emitted_insts su en` by simp[APPEND_ASSOC] >>
  `EVERY (\i. i.inst_id IN frag_ids su en /\ i.inst_opcode <> INVOKE /\
      i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
      (emitted_insts su en)` by
    simp[frag_ids_def, mk_inst_def, is_terminator_def] >>
  `create_operand_at su u` by simp[create_operand_at_def] >>
  `create_operand_full_scope su en explicit ctx func u []
      (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts))` by
    (irule create_admin_sequence_scope >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_assum `create_operand_full_scope _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [create_operand_full_scope_def]) >>
  qexistsl_tac [`Gz`,`tz`] >> asm_rewrite_tac[]
QED
