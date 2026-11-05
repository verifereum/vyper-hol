(* Counted address/data prefix interfaces. Source list evaluation forces
   every operand; use the existing eval_exprs_cons_action bridge. *)
Theory rawCallOperandPrefixPtr
Ancestors
  rawCallShapePtr typedOperandsPtr rawCallBufferPtr gasContext exprSimWordArgs
  exprSimDefs gasSummaryComposePtr vyperState vyperInterpreter exprSimHash

Theorem eval_exprs_head_admissible:
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[eval_exprs_cons_action, bind_def] >> metis_tac[]
QED

Theorem eval_exprs_tail_admissible:
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := marks ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc))
    (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_gas_obs, gas_admissible_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[] >>
  qpat_x_assum `!gs res ee. _` (qspec_then `marks ++ gs` mp_tac) >>
  simp[eval_exprs_cons_action, bind_def] >> metis_tac[]
QED

Theorem raw_call_addr_data_values:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  (do r <- eval_expr cx a; read_result cx r od) es = (INL av,es1) /\
  (do r <- eval_expr cx d; read_result cx r od) es1 = (rr,es2) ==>
  expr_sim_inv cenv cx env es1 /\ expr_sim_inv cenv cx env es2 /\
  expr_res_ok rr /\ value_has_type (BaseTV AddressT) av /\
  ?cap. expr_type d = BaseT (BytesT (Dynamic cap)) /\
    (!v. rr = INL v ==> ?bs. v = BytesV bs)
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  `expr_body_pre cenv cx env d es1` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_base_result >>
  simp[] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]
QED

Theorem forced_base_marked_facts:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  body_exprs_ptr_ok cx (e::args) /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    marks (INL v) mid (OK t) ==>
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  value_has_type (BaseTV bt) v /\ body_exprs_ptr_ok cx args /\
  gas_admissible (eval_exprs cx args)
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc))
    (mid with gas_obs := []) /\ ~t.vs_halted
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `(do r <- eval_expr cx e; read_result cx r od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by fs[bind_def] >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  `body_exprs_ptr_ok cx args` by
    (fs[bodyPtrPredsTheory.body_exprs_ptr_ok_def, bind_def, AllCaseEqs()] >>
     metis_tac[]) >>
  fs[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
  drule_all eval_exprs_tail_admissible >>
  simp[gas_admissible_gas_obs] >>
  metis_tac[fragGasPathTheory.gas_path_normal]
QED

Theorem forced_base_outcome_facts:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  body_exprs_ptr_ok cx (e::args) /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q R /\
  (!res ee G tn t. Q res ee G tn t ==> ?v. res = INL v) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\ ee.gas_obs = [] /\
      expr_sim_inv cenv cx env ee /\
      (?v. res = INL v /\ value_has_type (BaseTV bt) v) /\
      body_exprs_ptr_ok cx args /\
      gas_admissible (eval_exprs cx args)
        (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) ee /\
      ~t.vs_halted) R
Proof
  strip_tac >> irule operandOutcomePtrTheory.gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `?v. res = INL v` by metis_tac[] >> gvs[] >>
  drule_all forced_base_marked_facts >> simp[]
QED

Theorem body_base_operand_outcome_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (e::args) /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT bt /\
  gas_admissible (eval_exprs cx (e::args))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv dep cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?v. rr = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv dep cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\ ee.gas_obs = [] /\
      expr_sim_inv cenv cx env ee /\ value_has_type (BaseTV bt) v /\
      body_exprs_ptr_ok cx args /\
      gas_admissible (eval_exprs cx args)
        (\res. case res of INL vs => T | INR exc => expr_res_ok (INR exc)) ee /\
      ~t.vs_halted)
    (\rr ee gt r. expr_exit rr r)
Proof
  strip_tac >>
  `expr_sim_ptr dep ctx PG func cenv cx ty e es` by
    (fs[bodyPtrPredsTheory.body_exprs_ptr_ok_def,
        bodyPtrPredsTheory.body_expr_ptr_ok_def] >> metis_tac[]) >>
  drule eval_exprs_head_admissible >> strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.expr_sim_ptr_def] >>
  disch_then (drule_all_then assume_tac) >>
  drule forced_base_outcome_facts >>
  disch_then (drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`bt`, `args`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then assume_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ (\res ee G tn t. ?v. _) _` kall_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  POP_ASSUM_LIST (K all_tac) >> simp[] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED
