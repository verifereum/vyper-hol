Theory exprSimAbiEncodeWordResult
Ancestors
  exprSimAbiEncodeWordSuccess exprSimAbiEncodeTupleResult
  exprSimAbiEncodeNonwordResult exprSimAbiEncodeBytesOwnership
  exprSimAbiEncodeStagedObserver exprSimAbiEncodeCapacity
  exprSimHypsDefs vyperTypeSystem vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeInvariants vyperABI
  abiBuiltinEncodeCode abiBuiltinEncodeContext abiBuiltinEncodeMethod abiBuiltinEncodeSource
  abiBuiltinEncodeRun loweringPosts compileEnv words list fragGasMode exprLoweringProps

Theorem abi_encode_word_observation_vv_post:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) target [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  LENGTH (enc ct rv) = 32 /\
  expr_type (TypeBuiltin ann (AbiEncode F mid0) target [e]) = BaseT (BytesT (Dynamic N)) /\
  LENGTH (abi_encode_method_id_bytes mid0 ++ enc ct rv) <= N /\
  lower_abi_encode F mid src ei 32 staged = (out,final) /\
  fn_has_code staged final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce staged /\ local_ptrs_reserved ce origin /\
  origin.cs_next_id <= staged.cs_next_id /\
  abi_encode_staged_observation ctx func ce cx es' staged out mid
    (32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) p ct rv s actual /\
  wb_frame ce es es' origin s0 actual ==>
  vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid0) target [e])
    es origin final s0 es' (Value (BytesV (abi_encode_method_id_bytes mid0 ++ enc ct rv)))
    (LocatedValue (expr_type (TypeBuiltin ann (AbiEncode F mid0) target [e]))
      <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `well_typed_type_builtin_args (AbiEncode F mid0) target [expr_type e]` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  qpat_assum `abi_encode_staged_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encode_staged_observation_def] >> strip_tac >>
  drule_all abi_encode_tuple_result_memory >> disch_then (qspec_then `N` assume_tac) >>
  `!name b n. local_region ce es'.scopes actual name b n ==>
    p+(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) <= b \/ b+n <= p` by
    (drule lower_abi_encode_trace >> strip_tac >>
     drule_all abi_builtin_encode_code >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     irule abi_encode_setup_row_local_exclusion >>
     qpat_assum `abi_builtin_encode_setup _ _ _ = _` (irule_at Any) >>
     qpat_assum `stmt_state_rel ctx func ce cx es' actual` (irule_at Any) >>
     metis_tac[]) >>
  drule abi_encode_strict_id_growth >> strip_tac >>
  irule abi_encode_bytes_vv_post >> goal_assum (drule_at Any) >>
  simp[read_result_def, return_def] >>
  qexistsl [`staged.cs_next_id`, `p`, `32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))`] >>
  `p < dimword (:256)` by decide_tac >>
  simp[] >> Cases_on `mid0` >>
  gvs[abi_encode_method_id_bytes_def, well_typed_type_builtin_args_def,
    vfmConstantsTheory.word_size_def] >> gvs[]
QED

Theorem abi_encode_word_counted_success:
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) target [e]) es /\
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  evaluate_type_builtin cx (AbiEncode F mid0) target [expr_type e] [v] = INL result /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  lower_abi_encode F mid buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e)) 32 sh = (out,final) /\
  fn_has_code sa sh func /\ fn_has_code sh final func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce origin /\ origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?actual. gas_marked_path F ctx func s 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid0) target [e])
      es origin final s0 es' (Value result)
      (LocatedValue (expr_type (TypeBuiltin ann (AbiEncode F mid0) target [e]))
        <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_word_staged_counted >> strip_tac >>
  qpat_assum `expr_body_pre ce cx env e es`
    (mp_then Any strip_assume_tac exprSimHypsTheory.expr_body_pre_physical_type) >>
  `lowered_value_type ce e = expr_type e` by
    (Cases_on `expr_type e` >> Cases_on `lowered_value_type ce e` >>
     gvs[is_word_type_def, arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[is_word_type_def, arg_type_fits_def] >>
     Cases_on `b` >> Cases_on `b''` >>
     gvs[is_word_type_def, arg_type_fits_def]) >>
  qpat_assum `evaluate_type _ (expr_type e) = SOME tv` mp_tac >>
  qpat_assum `lowered_value_type ce e = expr_type e`
    (fn th => once_rewrite_tac[GSYM th]) >>
  disch_tac >>
  drule_all abi_encode_nonword_result_bound >> strip_tac >>
  `result = BytesV (abi_encode_method_id_bytes mid0 ++ enc ct rv)` by
    (qpat_assum `evaluate_type_builtin _ _ _ _ _ = _` mp_tac >>
     qpat_assum `vyper_to_abi _ _ _ = _` mp_tac >>
     qpat_assum `enc ct rv = _` mp_tac >>
     qpat_assum `ty = TupleT _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[evaluate_type_builtin_def, needs_external_call_wrap_def,
       evaluate_abi_encode_bytes_def]) >>
  suspend "finish"
QED

Resume abi_encode_word_counted_success[finish]:
  `local_ptrs_reserved ce sh /\ origin.cs_next_id <= sh.cs_next_id` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule abiBuiltinEncodeWordTheory.abi_builtin_encode_word_stage_shape >> strip_tac >>
     first_x_assum drule >> strip_tac >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
     decide_tac) >>
  `LENGTH (abi_encode_method_id_bytes mid0 ++ enc ct rv) <= N` by metis_tac[] >>
  drule_all abi_encode_word_observation_vv_post >> disch_tac >>
  qexists `actual` >> reverse conj_tac >- metis_tac[] >>
  `0 = 0 + 0` by simp[] >> pop_assum (fn th => once_rewrite_tac[th]) >>
  irule gas_marked_path_then >> qexists `initial` >> asm_rewrite_tac []
QED

Finalise abi_encode_word_counted_success
