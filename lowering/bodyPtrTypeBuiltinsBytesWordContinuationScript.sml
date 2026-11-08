Theory bodyPtrTypeBuiltinsBytesWordContinuation
Ancestors bodyPtrTypeBuiltinsBytesWordContinue bodyPtrTypeBuiltinsBytesWordTypes
  bodyPtrSignedConvertUintContinue bodyPtrSignedConvertSourceTyping
  bodyPtrDefs fragGasPathPtr gasSummaryComposePtr exprLowering exprLoweringProps
  loweringPosts compileEnv venomState
Libs monadsyntax

Theorem bytes_word_continuation_ptr:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  valid_conversion (expr_type e) dst /\ well_formed_type tenv dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0)
   then out = Lit 0w /\ sb = sa
   else compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,sb)) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\
  expr_post ctx fn cenv cx e es ca sa s0 (ee with gas_obs := []) v x s /\
  ptr_val_ok cx (expr_type e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\ ghost_kept cenv es ca G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ca.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr (cx_dead cx) tops (ctx,fn) PG
    (\st. (convert_result cx (expr_type e) dst v,st)) (ee with gas_obs := [],s,G,tn)
    (\res fin H th u. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0 fin vout out u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th u /\
      ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e])) vout out H th u /\
      (~is_word_type (post_value_type cenv (TypeBuiltin dst Convert dst [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out H u) /\
      ghost_kept cenv es ca G0 tn0 s0 H th)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e = BaseT (StringT 0)`
  >- ((Q.SUBGOAL_THEN `v = BytesV [] \/ v = StringV []` assume_tac
        >- (drule_all body_source_lowered_zero_empty >> simp[])) >>
      `is_word_type dst` by
        (drule_all bytestring_scalar_unsigned_convert_op >> simp[]) >>
      drule_all zero_scalar_continuation >>
      disch_then (qspec_then `PG` assume_tac) >>
      `out = Lit 0w /\ sb = sa` by metis_tac[] >>
      qpat_x_assum `out = _` SUBST_ALL_TAC >>
      qpat_x_assum `sb = _` SUBST_ALL_TAC >>
      simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_summary_ptr_at_conseq >> goal_assum (drule_at Any) >>
      simp[] >> rpt gen_tac >> strip_tac >>
      gvs[vyperASTTheory.expr_type_def]) >>
  `lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
   lowered_value_type cenv e <> BaseT (StringT 0)` by metis_tac[] >>
  `compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,sb)` by fs[] >>
  drule_all bytes_word_nonzero_outcome_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] mp_tac) >> simp[]
QED
