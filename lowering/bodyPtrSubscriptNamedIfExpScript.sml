(* Compiler preparation for the constructive named conditional pilot. *)
Theory bodyPtrSubscriptNamedIfExp
Ancestors
  bodyPtrSubscriptNamedArm bodyPtrSubscriptNamedFrame bodyPtrSubscriptNamedScalar
  exprSimIfExp exprSimOperators exprLoweringProps
  bodyPtrSubscriptBranchWitness fragExec emitHelper emitHelperProps compileEnv
  exprSimSource exprSimHypsDefs vyperTypeSystem vyperTypeEnv vyperTypeInvariants
  vyperValue vyperAST vyperTypeValues bodyPtrDefs loweringPosts stmtAssertPtr stmtFragPtr
  stmtSimIfProps valueEncoding venomState fragGasPathPtr ptrDiscipline
  vyperInterpreter vyperState loweringSlice vyperLookup gasSummary

(* Select the compiler arm, not an independently chosen execution witness. *)
Theorem word_ifexp_selected_states:
  compile_expr cenv ty (IfExp t c a b) sa = (vv,sb) /\ is_word_type t ==>
  ?cop s1 s5 s6 x6 s7 rv tl el xl bs bm bn bo lbl bx bp eop.
    lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,s1) /\
    emit_inst JNZ [cop; Label tl; Label el] [] s5 = ((),s6) /\
    new_block tl s6 = (x6,s7) /\
    lower_value compile_expr cenv ty (if bv then a else b) bs = (eop,bm) /\
    emit_inst ASSIGN [eop] [rv] bm = ((),bn) /\
    emit_inst JMP [Label xl] [] bn = ((),bo) /\
    new_block lbl bo = (bx,bp) /\
    vv = StackValue t (Var rv) /\
    s5.cs_current_bb = s1.cs_current_bb /\
    s5.cs_current_insts = s1.cs_current_insts /\
    bs.cs_current_bb = (if bv then tl else el) /\
    bs.cs_current_insts = [] /\ sb.cs_current_bb = xl /\
    sb.cs_current_insts = [] /\
    cs_extends sa s1 /\ cs_extends s1 s5 /\ cs_extends s7 bs /\
    cs_extends bs bm /\ cs_extends bp sb /\
    cs_extends s6 s7 /\ cs_extends bm bn /\ cs_extends bn bo /\
    cs_extends bo bp /\ cs_extends s5 s6 /\
    cs_extends sa bs /\ cs_extends bm sb /\
    cs_extends s7 sb /\ cs_extends bn sb /\ cs_extends bo sb /\
    cs_extends s6 sb /\ cs_extends s5 sb /\ cs_extends s1 sb /\
    (fn_has_code sa sb func ==>
      fn_has_code sa s1 func /\ fn_has_code s5 s6 func /\
      fn_has_code s6 s7 func /\ fn_has_code bs bm func /\
      fn_has_code bm bn func /\ fn_has_code bn bo func /\
      fn_has_code bo bp func) /\
    bo.cs_blocks = bn.cs_blocks /\ bo.cs_current_bb = bn.cs_current_bb /\
    bo.cs_current_insts = bn.cs_current_insts ++
      [mk_inst bn.cs_next_id JMP [Label xl] []] /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= bs.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= bs.cs_next_id /\
    bm.cs_next_id <= sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> x <> rv)
Proof
  strip_tac >> drule compile_expr_ifexp_states >>
  impl_tac >- metis_tac[cj 2 compile_expr_grows] >>
  strip_tac >>
  `lower_value compile_expr cenv ty a s7 = (aop,s8)` by
    (irule ifexp_arm_lower_value >> simp[] >> metis_tac[]) >>
  `lower_value compile_expr cenv ty b s11 = (bop,s12)` by
    (irule ifexp_arm_lower_value >> simp[] >> metis_tac[]) >>
  imp_res_tac cs_extends_emit_inst >> imp_res_tac cs_extends_new_block >>
  imp_res_tac emit_inst_extends >>
  Cases_on `bv`
  >- (qexistsl_tac [`cond_op`, `s1`, `s5`, `s6`, `x6`, `s7`, `rv`, `tl`, `el`, `xl`,
         `s7`, `s8`, `s9`, `s10`, `el`, `x10`, `s11`, `aop`] >>
      simp[] >> suspend "true") >>
  qexistsl_tac [`cond_op`, `s1`, `s5`, `s6`, `x6`, `s7`, `rv`, `tl`, `el`, `xl`,
    `s11`, `s12`, `s13`, `s14`, `xl`, `x14`, `sb`, `bop`] >>
  simp[] >> suspend "false"
QED

Resume word_ifexp_selected_states[true]:
  rpt strip_tac >>
  rpt (qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac) >>
  metis_tac[cs_extends_trans, cs_extends_refl, fn_has_code_mid]
QED

Resume word_ifexp_selected_states[false]:
  rpt strip_tac >>
  rpt (qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac) >>
  metis_tac[cs_extends_trans, cs_extends_refl, fn_has_code_mid]
QED

Finalise word_ifexp_selected_states

Theorem named_ifexp_preparation:
  expr_body_pre cenv cx env
    (IfExp t (Name ct ci) (Name at ai) (Name bt bi)) es ==>
  ct = BaseT BoolT /\ at = t /\ bt = t /\
  expr_body_pre cenv cx env (Name ct ci) es /\
  expr_body_pre cenv cx env (Name at ai) (es with gas_obs := []) /\
  expr_body_pre cenv cx env (Name bt bi) (es with gas_obs := [])
Proof
  strip_tac >> drule expr_body_pre_ifexp >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  gvs[expr_type_def]
QED

Theorem named_bool_value:
  expr_body_pre cenv cx env (Name (BaseT BoolT) id) es ==>
  ?entry bv. lookup_scopes id es.scopes = SOME entry /\ entry.value = BoolV bv
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
   evaluate_type (get_tenv cx) (BaseT BoolT) = SOME entry.type /\
   value_has_type entry.type entry.value` by
    (fs[expr_body_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  gvs[evaluate_type_def, value_has_type_BoolTV]
QED

Theorem named_ifexp_scalar_path:
  expr_body_pre cenv cx env
    (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)) es /\
  is_word_type t /\
  compile_expr cenv ty
    (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)) sa = (vv,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?rv ce bv ae Gf tnf sf.
    lookup_scopes ci es.scopes = SOME ce /\ ce.value = BoolV bv /\
    lookup_scopes (if bv then ai else bi) es.scopes = SOME ae /\
    vv = StackValue t (Var rv) /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    expr_post ctx func cenv cx
      (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)) es sa sb s
      (es with gas_obs := []) ae.value (Var rv) sf /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (es with gas_obs := []) Gf tnf sf /\
    ptr_val_ok cx t ae.value (Var rv) Gf tnf sf /\
    ghost_kept cenv es sa G tn s Gf tnf /\ op_prov Gf (Var rv) = NONE
Proof
  strip_tac >> drule named_ifexp_preparation >> strip_tac >>
  drule_all named_bool_value >>
  disch_then (qx_choose_then `ce` (qx_choose_then `bv` strip_assume_tac)) >>
  drule_all word_ifexp_selected_states >>
  disch_then (qspecl_then [`func`, `bv`] strip_assume_tac) >>
  `fn_has_code sa s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s6 s7 func /\ fn_has_code bs bm func /\
   fn_has_code bm bn func /\ fn_has_code bn bo func /\
   fn_has_code bo bp func` by metis_tac[] >>
  `is_word_type (BaseT BoolT)` by simp[is_word_type_def] >>
  drule_all named_word_scalar_path_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `gas_path_ptr _ 0 _ _ _ _ _ _ 0 Gc tnc (OK tt)` >>
  gvs[] >>
  suspend "continue"
QED

Resume named_ifexp_scalar_path[continue]:
  qpat_x_assum `expr_body_pre _ _ _ (IfExp _ _ _ _) _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (IfExp _ _ _ _) _ = _` kall_tac >>
  rpt (qpat_x_assum `cs_extends _ _` kall_tac) >>
  rpt (qpat_x_assum `new_block _ _ = _` kall_tac) >>
  `eval_operand cop tt = SOME (val_to_w256 (BoolV bv))` by
    metis_tac[if_condition_operand, expr_type_def] >>
  `op_taint tnc cop = {}` by fs[ptr_val_ok_def] >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG Gc tnc tt 0 Gc tnc
    (OK (jump_to (if bv then tl else el) tt))` by
    (irule assert_jnz_zero_path_ptr >>
     qpat_assum `emit_inst JNZ _ _ _ = _`
       (mp_then Any strip_assume_tac emit_inst_extends) >> simp[] >>
     qexistsl_tac [`cop`, `s5`, `s6`] >> simp[val_to_w256_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) tt` by
    fs[expr_post_def] >>
  `local_ptrs_reserved cenv bs /\ sa.cs_next_var <= bs.cs_next_var /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at bs x) /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at bs x)` by
    (conj_tac >- metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "arm"
QED

Resume named_ifexp_scalar_path[arm]:
  qpat_x_assum `lower_value _ _ _ (Name (BaseT BoolT) _) _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  `expr_body_pre cenv cx env (Name t (if bv then ai else bi))
     (es with gas_obs := []) /\
   lower_value compile_expr cenv ty (Name t (if bv then ai else bi)) bs = (eop,bm)` by
    (Cases_on `bv` >> gvs[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
     (jump_to bs.cs_current_bb tt) /\
   ghost_inv d cenv cx (es with gas_obs := []) Gc tnc
     (jump_to bs.cs_current_bb tt)` by
    fs[stmt_state_rel_jump_to, jump_to_def, ghost_inv_jump_to] >>
  `!x. not_fresh_at sa x ==> x <> rv` by metis_tac[] >>
  `bs.cs_current_bb = bs.cs_current_bb` by simp[] >>
  drule_all named_scalar_arm_continuation >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "finish"
QED

Resume named_ifexp_scalar_path[finish]:
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Gf tnf (OK sf)` by
    (qpat_x_assum `bs.cs_current_bb = _` (fn th => fs[th]) >>
     metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]) >>
  `!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)` by
    (fs[jump_to_def, lookup_var_def] >> metis_tac[]) >>
  `ghost_inv d cenv cx (es with gas_obs := []) Gf tnf sf /\
   ghost_kept cenv es sa G tn s Gf tnf` by
    (irule named_read_ghost_frame >> simp[jump_to_def] >> metis_tac[]) >>
  qexistsl_tac [`entry`, `Gf`, `tnf`, `sf`] >>
  simp[] >> suspend "post"
QED

Resume named_ifexp_scalar_path[post]:
  fs[] >>
  conj_asm1_tac
  >- (irule expr_post_ifexp >>
      simp[] >>
      qpat_assum `expr_post _ _ _ _ (Name (BaseT BoolT) _) _ _ _ _ _ _ _ _`
        (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ (Name t _) _ _ _ _ _ _ _ _`
        (irule_at Any) >> simp[expr_type_def]) >>
  simp[jump_to_def] >>
  fs[ptr_val_ok_def]
QED

Finalise named_ifexp_scalar_path

Theorem eval_named_ifexp:
  lookup_scopes ci es.scopes = SOME ce /\ ce.value = BoolV bv /\
  lookup_scopes (if bv then ai else bi) es.scopes = SOME ae ==>
  (vyperState$bind
    (eval_expr cx (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)))
    (read_result cx)) es = (INL ae.value, es)
Proof
  strip_tac >>
  `lookup_scopes_val ci es.scopes = SOME ce.value /\
   lookup_scopes_val (if bv then ai else bi) es.scopes = SOME ae.value` by
    (simp[lookup_scopes_val_SOME] >> metis_tac[]) >>
  simp[Once evaluate_def, switch_BoolV_def] >>
  Cases_on `bv` >> gvs[] >>
  simp[evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, read_result_def, read_place_def,
       read_memory_path_def, evaluate_subscripts_def, lift_sum_def,
       lift_option_type_def, ignore_bind_def, conditional_result_def,
       place_type_value_def, subscripts_type_def] >>
  IF_CASES_TAC >>
  simp[bind_def, get_scopes_def, return_def, read_result_def, read_place_def,
       evaluate_subscripts_def, lift_option_type_def, read_memory_path_def,
       lift_sum_def]
QED

Theorem named_ifexp_scalar_outcome:
  expr_body_pre cenv cx env
    (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)) es /\
  is_word_type t /\
  compile_expr cenv ty
    (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (vyperState$bind
    (eval_expr cx (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)))
    (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?rv. vv = StackValue t (Var rv) /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (vyperState$bind
      (eval_expr cx (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)))
      (read_result cx)) (es,s,G,tn)
    (\res ee Gf tnf sf. ?v. res = INL v /\
      expr_post ctx func cenv cx
        (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)) es sa sb s ee v (Var rv) sf /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee Gf tnf sf /\
      ptr_val_ok cx t v (Var rv) Gf tnf sf /\
      (~is_word_type t ==> ptr_buf_ok cenv
        (IfExp t (Name (BaseT BoolT) ci) (Name t ai) (Name t bi)) (Var rv) Gf sf) /\
      ghost_kept cenv es sa G tn s Gf tnf /\ op_prov Gf (Var rv) = NONE)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all named_ifexp_scalar_path >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexists_tac `rv` >> simp[] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL ae.value`, `es`, `Gf`, `tnf`, `OK sf`] >>
  simp[] >> gen_tac >>
  simp[gas_explicit_def] >> irule eval_named_ifexp >> simp[] >> metis_tac[]
QED
