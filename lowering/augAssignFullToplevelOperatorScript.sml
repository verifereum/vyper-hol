(* Joint numeric endpoint for the loaded top-level scalar and its RHS. *)
Theory augAssignFullToplevelOperator
Ancestors
  augAssignFullOperator augAssignPtrTypedNumeric augAssignPtrCompiler
  exprBopStraight exprBopSimProps exprLoweringProps stmtSimAssignStorageFacts
  stmtSimAugAssign vyperTypeBuiltins vyperTyping vyperTypeSystem
  exprSimSource exprSimUnwrap exprSimProps
  compileEnv ptrDiscipline venomExecSemantics venomState list finite_map pred_set

Theorem augassign_toplevel_operator_endpoint_full:
  compile_binop bop (Var out) op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op,s3) /\
  fn_has_code s2 s3 func /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  type_bits ty MOD 8 = 0 /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ value_has_type tvt cur /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\ value_has_type etv rhs /\
  word_value cur /\ word_value rhs /\
  (!n. expr_int_literal e = SOME n ==> rhs = IntV n) /\
  (bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n) /\
  (bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i) /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs es0) /\
  eval_operand (Var out) u = SOME (val_to_w256 cur) /\
  eval_operand op u = SOME (val_to_w256 rhs) /\
  op_prov Gr (Var out) = NONE /\ op_taint tnr (Var out) = {} /\
  op_prov Gr op = NONE /\ op_taint tnr op = {} /\
  not_fresh_at s2 out /\ (!z. op = Var z ==> not_fresh_at s2 z) /\
  (!l. op <> Label l) /\
  ~u.vs_halted /\ u.vs_current_bb = s2.cs_current_bb /\
  u.vs_inst_idx = LENGTH s2.cs_current_insts /\ ~ctx_has_dalloca ctx ==>
  (?result oprun operated Gop tnop.
    evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      tvt bop cur rhs = INL result /\
    word_value result /\ value_has_type tvt result /\
    encode_value tvt result = SOME [(0,val_to_w256 result)] /\
    run_inst_seq (emitted_insts s2 s3) u = OK oprun /\
    operated = oprun with vs_inst_idx := LENGTH s3.cs_current_insts /\
    operated = (u with vs_inst_idx := LENGTH s3.cs_current_insts)
      with vs_vars := operated.vs_vars /\
    eval_operand res_op operated = SOME (val_to_w256 result) /\
    (!z. not_fresh_at s2 z ==> lookup_var z operated = lookup_var z u /\
      FLOOKUP Gop z = FLOOKUP Gr z /\
      op_taint tnop (Var z) = op_taint tnr (Var z)) /\
    (!D lo. allocas_from lo u /\ lo <= u.vs_alloca_next ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gr,tnr) []
        (OK operated,Gop,tnop)) /\
    tnop.t_mem = tnr.t_mem /\ tnop.t_stor = tnr.t_stor /\
    tnop.t_trans = tnr.t_trans /\ tnop.t_imm = tnr.t_imm /\
    op_prov Gop res_op = NONE /\ op_taint tnop res_op = {}) \/
  (?msg abort_state abort_idx Gabort tnabort.
    evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      tvt bop cur rhs = INR (RuntimeError msg) /\
    (!D lo. allocas_from lo u /\ lo <= u.vs_alloca_next ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gr,tnr) []
        (Abort Revert_abort (abort_state with vs_inst_idx := abort_idx),Gabort,tnabort)))
Proof
  strip_tac >> `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  drule_all typed_binop_scalar_member_ptr >> strip_tac >>
  `straight_fresh (compile_binop bop (Var out) op ty NONE
    (if bop = Exp then expr_int_literal e else NONE))` by
    (irule compile_binop_straight_fresh_ptr >> simp[]) >>
  `!l. Var out <> Label l /\ op <> Label l` by simp[] >>
  drule_all compile_binop_clean_certificate_ptr >> strip_tac >>
  drule_at (Pat `expr_res_ok _`) binop_typed_numeric_witness >>
  disch_then (drule_at (Pat `well_typed_binop _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (qspecl_then [`if bop = Exp then expr_int_literal e else NONE`,
    `NONE`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_then assume_tac >>
  `!z. Var out = Var z ==> not_fresh_at s2 z` by simp[] >>
  drule_all binop_numeric_origin_ptr_continuation >>
  disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs es0 =
    case evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      tvt bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[] >> metis_tac[word_value_not_bytes]) >>
  strip_tac >- (disj1_tac >>
      rename1 `bop_result _ _ _ _ _ _ _ = INL result` >>
      `evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        tvt bop cur rhs = INL result` by
        (Cases_on `evaluate_binop
          (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
          tvt bop cur rhs` >>
         qpat_x_assum `_ = case _ of INL _ => _ | INR _ => _` mp_tac >>
         simp[]) >>
      `value_has_type tvt result` by
        (irule well_typed_binop_success_type >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
      `encode_value tvt result = SOME [(0,val_to_w256 result)]` by
        metis_tac[encode_value_word_typed, word_value_type_word,
          typed_val_to_w256_word_value] >>
      rename1 `run_inst_seq (emitted_insts s2 s3) u = OK oprun` >>
      qexistsl_tac [`result`, `oprun`,
        `oprun with vs_inst_idx := LENGTH s3.cs_current_insts`, `G'`, `tn'`] >>
      simp[eval_operand_def, lookup_var_def] >>
      (conj_tac >- (qpat_assum `oprun = _`
        (fn th => ONCE_REWRITE_TAC [th]) >> simp[])) >>
      metis_tac[lookup_var_def]) >>
  disj2_tac >> goal_assum (drule_at Any) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    tvt bop cur rhs` >> gvs[]
QED
