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
