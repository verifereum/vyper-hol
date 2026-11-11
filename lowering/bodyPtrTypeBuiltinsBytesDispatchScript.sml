Theory bodyPtrTypeBuiltinsBytesDispatch
Ancestors bodyPtrTypeBuiltinsConvertBind bodyPtrTypeBuiltinsBytesLayout
  bodyPtrTypeBuiltinsBytesWordContinuation bodyPtrTypeBuiltinsCastOperandContinuation
  bodyPtrTypeBuiltinsWidenOperandContinuation exprSimConvert exprSimSource
  exprSimHypsDefs vyperTypeSystem vyperTyping exprLowering compileEnv loweringStateRelDefs
  bodyPtrTypeBuiltinsBytesWordTypes bodyPtrTypeBuiltinsScalarSemantic
  bodyPtrTypeBuiltinsConvertOperandBoundary exprLoweringProps loweringPosts bodyPtrDefs
  memoryLocalRhsProps exprSimHyps exprOperandVar freshWrites exprSimConvertBytes valueCopyBytes
  bodyPtrTypeBuiltinsMemoryBounds bodyPtrTypeBuiltinsMemoryPlacement stmtLoweringMono
  bodyPtrTypeBuiltinsMemoryOperandSemantics bodyPtrTypeBuiltinsMemoryInterface

Theorem bytestring_convert_expr_sim_ptr:
  body_exprs_ptr_ok cx [e] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type (expr_type e) /\
  ~((?n. dst = BaseT (IntT n)) \/ dst = BaseT DecimalT) /\
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_convert >> strip_tac >>
  `e1 = e` by fs[] >> qpat_x_assum `e1 = e` SUBST_ALL_TAC >>
  qpat_x_assum `ann = dst` SUBST_ALL_TAC >>
  `well_formed_type env.type_defs dst` by
    (fs[expr_body_pre_def, well_typed_expr_def,
        well_typed_type_builtin_args_def, type_builtin_result_ok_def] >> metis_tac[]) >>
  (Q.SUBGOAL_THEN `is_bytestring_type dst \/ (is_word_type dst /\ !n. dst <> FlagT n)` assume_tac
   >- (Cases_on `is_bytestring_type dst` >> simp[] >>
     `is_word_type dst` by metis_tac[bytestring_scalar_unsigned_convert_op] >>
     conj_tac >- simp[] >>
     rpt strip_tac >> gvs[] >> drule scalar_flag_source_partition >>
     strip_tac >> gvs[is_bytestring_type_def])) >>
  irule convert_bind_expr_sim_ptr >> simp[] >>
  (reverse conj_tac >- metis_tac[]) >>
  qexists_tac `\x sa out cb.
    if is_bytestring_type dst then
      if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst
      then compile_bytestring_widen_copy (type_memory_bytes cenv dst) x
        (type_memory_bytes cenv (lowered_value_type cenv e)) sa = (out,cb)
      else compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,cb)
    else if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e = BaseT (StringT 0)
    then out = Lit 0w /\ cb = sa
    else compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,cb)` >>
  reverse conj_tac
  >- (rpt strip_tac >> drule lower_value_bytestring_convert_parts >>
      (impl_tac >- simp[]) >> strip_tac >> goal_assum (drule_at Any) >> simp[] >>
      drule bytestring_convert_suffix_extends >> simp[]) >>
  suspend "suffix"
QED

Resume bytestring_convert_expr_sim_ptr[suffix]:
  markerLib.RESUME_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type cenv e = expr_type e` by metis_tac[convert_operand_post_type] >>
  `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
  `ptr_buf_ok cenv e x G s` by metis_tac[] >>
  `expr_body_pre cenv cx env (TypeBuiltin dst Convert dst [e]) (es with gas_obs := gs)` by
    fs[expr_body_pre_gas_obs] >>
  `local_ptrs_reserved cenv sa` by
    (fs[local_ptrs_reserved_def] >> metis_tac[not_fresh_at_mono]) >>
  reverse (Cases_on `is_bytestring_type dst`)
  >- suspend "word" >>
  suspend "memory"
QED
Resume bytestring_convert_expr_sim_ptr[word]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    (`expr_body_pre cenv cx env e (es with gas_obs := gs)` by fs[expr_body_pre_gas_obs] >>
     drule_all (SRULE [SF ETA_ss] exprSimIfExpTheory.ifexp_body_pre_read_typed) >> simp[]) >>
  simp[vyperASTTheory.expr_type_def, SF ETA_ss] >>
  irule (SRULE [post_value_type_def, vyperASTTheory.expr_type_def, SF ETA_ss]
    (Q.INST [`ee` |-> `ee with gas_obs := []`] bytes_word_continuation_ptr)) >> simp[] >>
  `cx_tops cx = tops` by fs[bodySimTheory.body_inv_def, gasContextTheory.cx_tops_def] >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexistsl_tac [`sa`,`x`] >> simp[] >>
  `!z. x = Var z ==> not_fresh_at sa z` by metis_tac[compile_lower_value_var] >>
  fs[local_ptrs_reserved_def] >> metis_tac[not_fresh_at_mono]
QED

Resume bytestring_convert_expr_sim_ptr[memory]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `~is_word_type dst` by metis_tac[is_bytestring_word_type] >>
  `cx_tops cx = tops` by fs[bodySimTheory.body_inv_def, gasContextTheory.cx_tops_def] >>
  `type_alloc_ok cenv dst /\ type_alloc_ok cenv (expr_type e)` by
    (fs[expr_body_pre_def] >>
     metis_tac[alloc_limits_expr_type_alloc_ok, vyperASTTheory.expr_type_def]) >>
  `!n. dst = BaseT (BytesT (Dynamic n)) \/ dst = BaseT (StringT n) ==> n < dimword(:256)` by
    metis_tac[bytestring_alloc_capacity_bound] >>
  `!i. expr_type e = BaseT (BytesT (Dynamic i)) \/ expr_type e = BaseT (StringT i) ==> i < dimword(:256)` by
    metis_tac[bytestring_alloc_capacity_bound] >>
  `type_memory_bytes cenv dst < dimword(:256)` by metis_tac[bytestring_alloc_word_bound] >>
  `is_bytestring_type (lowered_value_type cenv e)` by
    (irule bodyPtrSignedConvertSourceTypingTheory.body_source_lowered_bytestring >> metis_tac[]) >>
  `32 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    metis_tac[bytestring_memory_header_bound] >>
  `!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p` by
    metis_tac[not_fresh_at_mono] >>
  `!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p` by
    metis_tac[not_fresh_at_mono] >>
  Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst`
  >- suspend "widen" >>
  `compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,cb)` by fs[] >>
  mp_tac (Q.SPECL [`expr_type e`,`dst`] memory_convert_shapes) >> simp[] >>
  disch_then (qx_choose_then `i` (qx_choose_then `n` assume_tac)) >>
  `compile_type_convert x (ConvBytestringCast n i) sa = (out,cb)` by metis_tac[] >>
  drule convert_cast_static_frame >> strip_tac >>
  `sa.cs_next_id <= cb.cs_next_id` by metis_tac[bytestring_cast_id_growth] >>
  drule_all straight_line_suffix_placement >> strip_tac >>
  simp[vyperASTTheory.expr_type_def, SF ETA_ss] >>
  irule (SRULE [post_value_type_def, vyperASTTheory.expr_type_def, SF ETA_ss]
    cast_convert_operand_continuation) >> simp[] >>
  rpt (goal_assum (drule_at Any) >> simp[]) >> metis_tac[]
QED
Resume bytestring_convert_expr_sim_ptr[widen]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `compile_bytestring_widen_copy (type_memory_bytes cenv dst) x
    (type_memory_bytes cenv (lowered_value_type cenv e)) sa = (out,cb)` by fs[] >>
  drule_all bytestring_widen_straight_line >> strip_tac >>
  drule_all straight_line_suffix_placement >> strip_tac >>
  `ca.cs_next_id <= sa.cs_next_id` by
    (mp_tac (cj 2 ci_mono_compile_expr_sa) >>
     disch_then (qspecl_then [`cenv`,`expr_type e`,`e`,`ca`] mp_tac) >>
     simp[ci_mono_def]) >>
  `local_ptrs_rel fn cenv es.scopes s0` by fs[stmt_state_rel_def, state_rel_def] >>
  simp[vyperASTTheory.expr_type_def, SF ETA_ss] >>
  irule (SRULE [post_value_type_def, vyperASTTheory.expr_type_def, SF ETA_ss]
    widen_convert_operand_continuation) >> simp[] >>
  rpt (goal_assum (drule_at Any) >> simp[]) >> metis_tac[]
QED
Finalise bytestring_convert_expr_sim_ptr
