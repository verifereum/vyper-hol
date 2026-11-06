(* Reusable raw-value to operand boundary for identity memory unwrap. *)
Theory reasonMemorySuccessPtr
Ancestors bodyPtrDefs exprSimUnwrap exprSimUnwrapProps loweringPosts
  reasonMemoryEncoderPtr reasonRaiseContinuationPtr stmtSimForArrayFrame
  vyperTypeSystem vyperAST supportedStmts exprSimHyps allocLimits compileEnv
  stmtSimReason stmtSimReasonExpr exprSimHypsDefs vyperValue
  exprOperandVar exprLoweringProps reasonResourcesPtr context

Theorem reason_stack_read_post_ptr:
  vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue ty op) s /\
  ptr_vv_ok cx (expr_type e) tv (StackValue ty op) ee G tn s /\
  read_result cx tv ee = (INL v,ee) ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s
Proof
  strip_tac >> drule vv_post_read_result >> strip_tac >>
  conj_tac
  >- (irule expr_post_of_vv_post_stack >> metis_tac[]) >>
  gvs[ptr_vv_ok_def]
QED

Theorem reason_memory_read_post_ptr:
  vv_post ctx func cenv cx e es sa sb s0 ee tv (LocatedValue ty p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty p) ee G tn s /\
  p.ptr_location = LocMemory /\ ~is_word_type ty /\
  read_result cx tv ee = (INL v,ee) ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v p.ptr_operand s /\
  ptr_val_ok cx (expr_type e) v p.ptr_operand G tn s
Proof
  strip_tac >> drule vv_post_read_result >> strip_tac >>
  conj_tac
  >- (irule expr_post_of_vv_post_memory >> metis_tac[]) >>
  gvs[vv_post_def, vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def]
QED

(* Only the source evaluation, not vv_post's frame, fixes the scope domains. *)
Theorem reason_success_scopes:
  supported_expr tops e /\
  ~supported_expr_exists expr_internal_call_root e /\
  (?gin gout. eval_expr cx e (es with gas_obs := gin) =
    (res, ee with gas_obs := gout)) ==>
  MAP FDOM es.scopes = MAP FDOM ee.scopes
Proof
  strip_tac >> drule_all supported_expr_scopes >> simp[]
QED


Theorem reason_supported_string_type:
  supported_string_reason tops e /\ well_typed_expr env e ==>
  ?cap. expr_type e = BaseT (StringT cap)
Proof
  strip_tac >>
  Cases_on `?ty str. e = Literal ty (StringL str)`
  >- (gvs[well_typed_expr_def, expr_type_def] >>
      rename1 `well_typed_literal ty (StringL _)` >>
      Cases_on `ty` >> fs[well_typed_literal_def] >>
      rename1 `BaseT b` >> Cases_on `b` >> fs[well_typed_literal_def]) >>
  `case expr_type e of BaseT (StringT _) => T | _ => F` by
    (Cases_on `e` >> fs[supported_string_reason_def] >>
     rename1 `Literal _ lit` >> Cases_on `lit` >>
     fs[supported_string_reason_def]) >>
  Cases_on `expr_type e` >> fs[] >>
  rename1 `BaseT b` >> Cases_on `b` >> fs[]
QED

Theorem reason_string_operand_var:
  ptr_val_ok cx (BaseT (StringT cap)) (StringV str) op G tn s /\
  evaluate_type (get_tenv cx) (BaseT (StringT cap)) =
    SOME (BaseTV (StringT cap)) /\
  eval_operand op s = SOME w ==>
  ?src. op = Var src
Proof
  simp[ptr_val_ok_def, is_word_type_def, ptr_mem_ok_def] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`BaseTV (StringT cap)`, `w`] mp_tac) >>
  simp[val_footprint_def] >> metis_tac[]
QED

Theorem reason_identity_read_post_ptr:
  reason_vv_ok vv /\
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  read_result cx tv ee = (INL v,ee) ==>
  ?op. reason_vv vv = SOME op /\
    (!st. unwrap_value cenv vv st = (op,st)) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
    ptr_val_ok cx (expr_type e) v op G tn s
Proof
  strip_tac >> gvs[reason_vv_ok_def] >>
  `!st. unwrap_value cenv vv st = (op,st)` by
    metis_tac[unwrap_value_reason_vv] >>
  Cases_on `vv` >> gvs[reason_vv_def, AllCaseEqs()] >>
  metis_tac[reason_stack_read_post_ptr, reason_memory_read_post_ptr]
QED

Theorem reason_memory_success_path_ptr:
  expr_body_pre cenv cx env r es /\
  supported_string_reason tops r /\ supported_expr tops r /\
  ~supported_expr_exists expr_internal_call_root r /\ reason_vv_ok vv /\
  compile_expr cenv (expr_type r) r sa = (vv,sm) /\
  compile_revert_with_reason cenv vv (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx r es sa sm s0 ee tv vv t /\
  ghost_inv d cenv cx ee G tn t /\
  ptr_vv_ok cx (expr_type r) tv vv ee G tn t /\
  read_result cx tv ee = (INL (StringV str),ee) /\
  (?gin gout. eval_expr cx r (es with gas_obs := gin) =
    (INL tv, ee with gas_obs := gout)) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?Gf tnf u. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 Gf tnf
    (Abort Revert_abort u)
Proof
  strip_tac >>
  `well_typed_expr env r /\ alloc_limits_expr cenv r` by
    fs[expr_body_pre_def] >>
  drule_all reason_supported_string_type >> strip_tac >>
  drule_all reason_identity_read_post_ptr >> strip_tac >>
  `evaluate_type (get_tenv cx) (BaseT (StringT cap)) =
    SOME (BaseTV (StringT cap))` by
    (drule expr_body_pre_type_evaluates >> simp[evaluate_type_def] >>
     rpt strip_tac >> gvs[]) >>
  `?w. eval_operand op t = SOME w` by fs[expr_post_def, expr_val_rel_def] >>
  `?src. op = Var src` by metis_tac[reason_string_operand_var] >>
  `type_alloc_ok cenv (BaseT (StringT cap))` by
    metis_tac[alloc_limits_expr_type_alloc_ok] >>
  `64 + type_memory_bytes cenv (BaseT (StringT cap)) < dimword (:256)` by
    metis_tac[reason_encoder_allocation_limit] >>
  `val_wf (BaseTV (StringT cap)) (StringV str)` by
    fs[expr_post_def, expr_val_at_def, is_word_type_def] >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `vv_operand vv = Var src` by
    (Cases_on `vv` >> gvs[reason_vv_def, vv_operand_def, AllCaseEqs()]) >>
  `not_fresh_at sm src` by
    (drule (cj 1 compiler_compile_var) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (irule reason_success_scopes >> metis_tac[]) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (REWRITE_RULE [GSYM AND_IMP_INTRO] reason_memory_encoder_path_ptr) >>
  rpt (disch_then drule) >>
  simp[is_word_type_def]
QED
