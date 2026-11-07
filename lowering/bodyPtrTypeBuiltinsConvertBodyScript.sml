(* Counted operand/suffix assembly for non-residual Convert. *)
Theory bodyPtrTypeBuiltinsConvertBody
Ancestors bodyPtrTypeBuiltinsConvertFrame bodyPtrTypeBuiltinsConvert vyperAST
  bodyPtrTypeBuiltinsOperands bodyPtrTypeBuiltinsMarkedBind
  bodyPtrTypeBuiltinsConvertMarked
  bodyPtrPreds bodyPtrDefs exprPtrUnwrap exprSimDefs gasSummaryComposePtr gasExemptCert
  exprSimConvert exprSimSource exprSimHyps exprLowering exprLoweringProps
  bodySim vyperState vyperInterpreter

Theorem expr_exit_exception_iff[local]:
  (?exc. (res : value + exception) = INR exc /\
    expr_exit (INR exc : value + exception) r) = expr_exit res r
Proof
  Cases_on `res` >> simp[expr_exit_def] >> REFL_TAC
QED

Theorem convert_expr_sim_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  ~(is_bytestring_type (expr_type e) /\
    ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) ==>
  expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann Convert typ [e]) es
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_convert >> simp[]) >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    (irule body_expr_ptr_ok_sim >> metis_tac[]) >>
  rewrite_tac[expr_sim_ptr_def] >> rpt strip_tac >>
  drule convert_lower_entry >> strip_tac >>
  drule_all convert_compiler_code_split >> strip_tac >>
  `gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[SF ETA_ss] >> strip_tac >>
  `ann = typ` by (drule expr_body_pre_convert >> simp[]) >>
  qpat_x_assum `ann = typ` SUBST_ALL_TAC >> simp[expr_type_def] >>
  pure_rewrite_tac[SRULE [SF ETA_ss] eval_expr_convert_action] >>
  irule gas_outcome_ptr_marked_bind >> conj_tac
  >- suspend "exempt_bind" >>
  conj_tac >- suspend "exempt_error" >>
  simp[expr_exit_exception_iff] >>
  qexists_tac `\v ee G tn t.
    expr_post ctx func cenv cx e es sa sm s0 ee v x t /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\ ptr_val_ok cx (expr_type e) v x G tn t /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn` >>
  simp[SF ETA_ss] >> suspend "normal"
QED

Resume convert_expr_sim_ptr[exempt_error]:
  rpt strip_tac >> irule gas_exempt_cert_error_value >> metis_tac[]
QED

Resume convert_expr_sim_ptr[exempt_bind]:
  rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]
QED

Resume convert_expr_sim_ptr[normal]:
  rpt strip_tac >> irule (SRULE [SF ETA_ss] convert_marked_normal_continuation) >>
  metis_tac[]
QED

Finalise convert_expr_sim_ptr

Theorem convert_compile_stack:
  !cenv ty ann typ e sa.
    ?op sb. compile_expr cenv ty (TypeBuiltin ann Convert typ [e]) sa =
      (StackValue ann op,sb)
Proof
  rpt gen_tac >> Cases_on `compile_expr cenv ty (TypeBuiltin ann Convert typ [e]) sa` >>
  drule convert_compile_entry >> strip_tac >> metis_tac[]
QED

Theorem convert_singleton_body_expr_ptr_ok:
  body_exprs_ptr_ok cx [e] /\
  ~(is_bytestring_type (expr_type e) /\
    ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) ==>
  body_expr_ptr_ok cx (TypeBuiltin ann Convert typ [e])
Proof
  strip_tac >>
  `body_expr_ptr_ok cx e` by fs[body_exprs_ptr_ok_def] >>
  rw[body_expr_ptr_ok_def] >>
  `expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann Convert typ [e]) es` by
    (irule convert_expr_sim_ptr >> metis_tac[]) >> simp[] >>
  irule expr_vv_sim_ptr_stack >> simp[] >> conj_tac
  >- metis_tac[convert_compile_stack] >>
  metis_tac[eval_expr_type_builtin_value]
QED

Theorem convert_nonresidual_body_expr_ptr_ok:
  (type_builtin_args_length_ok Convert (LENGTH args) ==> body_exprs_ptr_ok cx args) /\
  ~(?e. args = [e] /\ is_bytestring_type (expr_type e) /\
    ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) ==>
  body_expr_ptr_ok cx (TypeBuiltin ann Convert typ args)
Proof
  strip_tac >> Cases_on `LENGTH args = 1`
  >- (Cases_on `args` >> fs[] >> Cases_on `t` >> fs[] >>
      irule convert_singleton_body_expr_ptr_ok >>
      fs[vyperContextTheory.type_builtin_args_length_ok_def] >> metis_tac[]) >>
  irule bodyPtrTypeBuiltinsConvertEntryTheory.convert_arity_body_expr_ptr_ok >> simp[]
QED
