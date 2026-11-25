Theory entryCreateAbiSavedWordScope
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  abiEncodeValuesWordRow abiEncodeValuesCode bodyFullExtCallDirectWord
  placeMemoryCodeLayout emitHelperProps abiEncoderProps
  loweringShapeRules
  abiEncoderWindowPhase abiEncoderWindowSequence exprLoweringProps
  exprLowering context compileEnv venomState venomInst words list finite_map
  pred_set arithmetic pair

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
  drule_all bodyFullExtCallDirectStateTheory.abi_encode_saved_state_resources >>
  strip_tac >>
  drule_all abi_encode_saved_word_row_pure_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac)) >>
  qpat_x_assum `abi_word_row_run _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_word_row_run_def]) >>
  `create_operand_full_scope su en explicit ctx func u [] (OK z)` by
    (qpat_assum `z = _` SUBST1_TAC >>
     irule create_admin_sequence_scope >> simp[create_operand_at_def]) >>
  qpat_assum `create_operand_full_scope _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [create_operand_full_scope_def]) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >> metis_tac[]
QED
