(* Full body-level calibration for word Not. *)
Theory bodyPtrWordBuiltinsNotCase
Ancestors bodyPtrWordBuiltinsNotSuffix bodyPtrWordBuiltinsWitnessCompose
  gasSummaryComposePtr ptrDiscipline stmtFragPtr exprSimUnopComposeProps exprSimWordArgs
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps exprSimHypsDefs
  exprSimUnopProps exprSimProps exprSimSource exprPtrUnwrap exprLowering
  vyperAST vyperTypeSystem vyperTyping vyperInterpreter list
  fragGasFresh freshWrites varsExt exprSimDefs loweringPosts exprLoweringProps
  exprUnopStraight exprUnopSimDefs valueEncoding vyperValue vyperValueOperation
  vyperContext builtinProps arithmeticProps vyperArith integer_word words byte
  emitHelperProps emitHelper compileEnv venomExecSemantics venomInst venomState
Libs intLib

Theorem word_not_operand_pre:
  expr_body_pre cenv cx env (Builtin ty Not [e]) es ==>
  ty = expr_type e /\
  (is_bool_type (expr_type e) \/ is_uint256_type (expr_type e) \/
   is_bytes32_type (expr_type e) \/ is_flag_type (expr_type e)) /\
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `ty = expr_type e /\
   (is_bool_type (expr_type e) \/ is_uint256_type (expr_type e) \/
    is_bytes32_type (expr_type e) \/ is_flag_type (expr_type e))` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  simp[] >> drule expr_body_pre_builtin_arg >>
  disch_then irule >> gvs[expr_body_pre_def]
QED

Theorem word_not_typed_run:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/ is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
  ?v' w. unop_result cx ann Not tys v es = INL v' /\
    (!tv'. evaluate_type (get_tenv cx) ann = SOME tv' ==>
      w = typed_val_to_w256 tv' v') /\
    !x sa sb op s.
      (if ann = BaseT BoolT then emit_op ISZERO [x]
       else compile_invert x ann cenv) sa = (op,sb) /\
      fresh_vars_wrt sa s /\ eval_operand x s = SOME (typed_val_to_w256 tv v) ==>
      ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ eval_operand op t = SOME w
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP not_type_cases)
    strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
      vyperASTTheory.type_to_int_bound_def, typed_val_to_w256_def,
      val_to_w256_def, compile_invert_def, vyperValueTheory.evaluate_type_def]
  >~ [`emit_op ISZERO`]
  >- (rpt strip_tac >> drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
      qexists_tac `ss'` >> asm_rewrite_tac[] >>
      Cases_on `b` >> gvs[bool_to_word_def])
  >~ [`i2w _`]
  >- (rename1 `Num i` >> rpt strip_tac >>
      drule_all emit_op_NOT_correct >> rw[] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def])
  >~ [`PAD_RIGHT`]
  >- (rename1 `LENGTH bs = 32` >> rpt strip_tac >> gvs[listTheory.PAD_RIGHT] >>
      drule_all emit_op_NOT_correct >> rw[] >>
      simp[listTheory.PAD_RIGHT, length_word_to_bytes_be, word_of_bytes_be_to_bytes]) >>
  rename1 `k < 2 ** m` >> rpt strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) emit_op_pure2_correct >>
  simp[eval_operand_def] >>
  disch_then (qspec_then `word_xor` mp_tac) >>
  disch_then (qspecl_then [`n2w k`, `s`] mp_tac) >>
  impl_tac
  >- (simp[] >> irule step_XOR >> simp[eval_operand_def]) >>
  strip_tac >> qexists_tac `ss'` >> simp[flag_not_xor]
QED

Theorem word_not_typed_post:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/ is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  (if ann = BaseT BoolT then emit_op ISZERO [x]
   else compile_invert x ann cenv) s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  ~t0.vs_halted /\ t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var ==>
  ?v' t. unop_result cx ann Not tys v ee = INL v' /\
    run_inst_seq (emitted_insts s1 sb) t0 = OK t /\
    expr_post ctx func cenv cx (Builtin ann Not [e]) es sa sb s0 ee v' op
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `is_word_type ann` by
    (drule not_type_cases >> strip_tac >> gvs[is_word_type_def]) >>
  `stmt_state_rel ctx func cenv cx ee t0` by gvs[expr_post_def] >>
  `straight_fresh (if ann = BaseT BoolT then emit_op ISZERO [x]
    else compile_invert x ann cenv)` by
    (drule not_type_cases >> strip_tac >> gvs[compile_invert_def] >>
     irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
  drule_all word_not_typed_run >>
  disch_then (qspecl_then [`tys`, `ee`] strip_assume_tac) >>
  qpat_x_assum `!x sa sb op s. _` drule >>
  disch_then (qspec_then `drop_fresh s1 t0` mp_tac) >>
  (impl_tac >- simp[fresh_vars_wrt_drop_fresh, eval_operand_drop_fresh]) >>
  strip_tac >> drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  rename1 `run_inst_seq _ t0 = OK actual` >>
  qexistsl [`v'`, `actual`] >> simp[] >>
  irule expr_post_unop >> simp[] >>
  conj_tac
  >- (simp[expr_val_rel_def] >> rpt strip_tac >> gvs[]) >>
  qexistsl [`s1`, `t0`, `v`, `x`] >> gvs[]
QED

Theorem word_not_emit_form:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/ is_flag_type ann) /\
  op_taint tn x = {} ==>
  ?opc args.
    (if ann = BaseT BoolT then emit_op ISZERO [x]
     else compile_invert x ann cenv) = emit_op opc args /\
    MEM opc [ISZERO; NOT; XOR] /\
    (!arg. MEM arg args ==> op_taint tn arg = {})
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP not_type_cases)
    assume_tac) >>
  gvs[compile_invert_def]
  >~ [`emit_op ISZERO _`]
  >- (qexistsl [`ISZERO`, `[x]`] >> simp[]) 
  >~ [`emit_op XOR _`]
  >- (qexistsl [`XOR`, `[x; Lit (n2w (2 ** cenv.ce_flag_n_members (nsid_to_string nsid) - 1))]`] >>
      rpt strip_tac >> gvs[] >> simp[ptrDisciplineTheory.op_taint_def]) >>
  qexistsl [`NOT`, `[x]`] >> simp[]
QED

Theorem word_not_emit_run_step:
  MEM opc [ISZERO; NOT; XOR] /\ emit_op opc args s1 = (op,sb) /\
  run_inst_seq (emitted_insts s1 sb) t0 = OK t ==>
  step_inst_base
    (mk_inst s1.cs_next_id opc args [STRING #"%" (toString s1.cs_next_var)]) t0 = OK t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()]
QED

Theorem word_not_typed_ptr_outcome:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/ is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  (if ann = BaseT BoolT then emit_op ISZERO [x]
   else compile_invert x ann cenv) s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ptr_val_ok cx ann v x G tn t0 /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (unop_result cx ann Not [expr_type e] v vs,vs)) (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann Not [e]) es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all word_not_typed_post >>
  disch_then (qspec_then `[expr_type e]` strip_assume_tac) >>
  `op_taint tn x = {}` by gvs[ptr_val_ok_def] >>
  drule_all word_not_emit_form >>
  disch_then (qspec_then `cenv` strip_assume_tac) >>
  qpat_x_assum `_ = emit_op opc args` SUBST_ALL_TAC >>
  drule_all word_not_emit_run_step >> strip_tac >>
  drule_all word_not_emit_cursor >> strip_tac >>
  `is_word_type ann` by
    (drule not_type_cases >> strip_tac >> gvs[is_word_type_def]) >>
  irule gas_outcome_ptr_conseq >>
  qexistsl [`\res fin G' tn' u.
    (res = INL v' /\ fin = ee with gas_obs := [] /\
     expr_post ctx func cenv cx (Builtin ann Not [e]) es sa sb s0 fin v' op u /\
     u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
    ghost_inv d cenv cx ee G' tn' u /\ ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE`,
    `\res fin gt r. expr_exit res r`] >>
  conj_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      gvs[ghost_inv_gas_obs, ptr_val_ok_def]) >>
  conj_tac >- simp[] >>
  ho_match_mp_tac (Q.INST [`sa` |-> `s1`, `sc` |-> `sa`, `res` |-> `INL v'`]
    word_not_emit_outcome) >> simp[allocas_from_def, exprSimUnopComposePropsTheory.unop_result_gas_obs] >>
  conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ (Builtin _ _ _) _ _ _ _ _ _ _ _` mp_tac >>
      simp[expr_post_def, expr_val_at_def, stmt_state_rel_gas_obs] >>
      metis_tac[]) >>
  drule_all word_not_normal_update >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[update_var_def]
QED
