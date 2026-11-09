Theory bodyPtrTypeBuiltinsBytesWordAbort
Ancestors bodyPtrTypeBuiltinsBytesWordInputs bodyPtrTypeBuiltinsBytesWordTypes
  bodyPtrTypeBuiltinsBytesWordCounted bodyPtrTypeBuiltinsUintCounted
  bodyPtrSignedConvertSourceTyping bodyPtrDefs exprLowering exprLoweringProps
  loweringPosts compileEnv venomState

Theorem bytes_word_abort_counted:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  valid_conversion (expr_type e) dst /\ well_formed_type tenv dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type cenv e <> BaseT (StringT 0) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  ptr_val_ok cx (expr_type e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es ca G0 tn0 s0 G tn /\
  ca.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?H th j. gas_path_ptr D 0 ctx fn PG G tn s 0 H th
    (Abort err (t with vs_inst_idx := j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (drule_all body_source_lowered_nonzero_capacity >> simp[]) >>
  drule_all bytes_word_child_memory_inputs >> strip_tac >>
  qpat_x_assum `x = Var _` SUBST_ALL_TAC >>
  `not_fresh_at sa src` by simp[] >>
  drule_all bytestring_scalar_type_partition >> strip_tac >>
  drule_all bodyPtrSignedConvertSourceTypingTheory.bytestring_typed_value_view >> strip_tac >>
  gvs[mk_convert_op_def, is_bytestring_type_def, vyperValueTheory.evaluate_type_def,
      vyperTypeSystemTheory.well_formed_type_def]
  >>~- ([`compile_type_convert _ ConvBytestringToBool _ = _`],
    drule_at (Pat `compile_type_convert _ _ _ = _`) bytes_word_pure_no_abort >>
    simp[] >> metis_tac[])
  >>~- ([`compile_type_convert _ (ConvBytestringToBytesM _) _ = _`],
    drule_at (Pat `compile_type_convert _ _ _ = _`) bytes_word_pure_no_abort >>
    simp[] >> metis_tac[]) >>
  irule (SRULE [mk_convert_op_def, is_bytestring_type_def]
    bytes_uint_counted_abort) >>
  rpt (goal_assum (drule_at Any) >> simp[]) >>
  simp[vyperValueTheory.evaluate_type_def] >> metis_tac[]
QED
