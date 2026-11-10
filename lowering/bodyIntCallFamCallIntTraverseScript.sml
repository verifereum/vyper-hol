(* Concrete pure-argument traversal, retaining deferred value certificates. *)
Theory bodyIntCallFamCallIntTraverse
Ancestors
  bodyIntCallFamCallIntTraverseChild bodyIntCallFamCallIntTraverseInterfaces
  bodyIntCallFamCallIntCertificateIntro bodyIntCallJointCallCore
  bodyIntCallJointContract exprSimMemDefs supportedExprTraverse

val deferred = ``\fp ce e vv r b es s.
  ?a. vv_holds ce fp.jc_cx (post_value_type ce e) r vv es s /\
    vv_at ce fp.jc_cx (post_value_type ce e) a b es r vv s /\
    (post_value_type ce e <> expr_type e ==>
      vv_own ce fp.jc_cx (post_value_type ce e) a b es r vv s) /\
    vv_storage_live fp.jc_cx vv es s /\
    (!x. vv_operand vv = Var x ==> not_fresh_at b x) /\
    (post_value_type ce e <> NoneT /\
     ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) /\
     (case vv of StackValue _ _ => T
               | LocatedValue _ p => p.ptr_location = LocMemory) ==>
     !tv. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv ==>
       ?w off len. eval_operand (vv_operand vv) s = SOME w /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + len /\
         off + len < dimword (:256) /\
         (fp.jc_lo <= off \/
          ?base size. fp.jc_staged base size /\ base <= off /\
                      off + len <= base + size))``;
val deferred_list = ``\fp ce ds vs rs b es s.
  LENGTH ds = LENGTH vs /\ LENGTH ds = LENGTH rs /\
  !i. i < LENGTH ds ==>
    ^deferred fp ce (EL i ds) (EL i vs) (EL i rs) b es s``;

Theorem intcall_deferred_child_run:
  intcall_expr_producer fp child /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env child ee /\
  supported_pure_expr fp.jc_tops child /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr child) /\
  compile_expr ce (expr_type child) child b = (vv,d) /\
  fn_has_code b d fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (eval_expr fp.jc_cx child) expr_vv_res_ok ee /\
  intcall_expr_res fp ce env ee b t /\ ~t.vs_halted /\
  t.vs_current_bb = b.cs_current_bb /\
  t.vs_inst_idx = LENGTH b.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx child) (ee,t)
    (\res ef u. ?r. res = INL r /\
      ^deferred fp ce child vv r d ef u /\
      vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx child ee b d t ef r vv u /\
      intcall_expr_cont fp ce env ee b t ef d u)
    (\res ef r. expr_exit res r)
Proof
  strip_tac >>
  `supportedExprs$supported_expr fp.jc_tops child` by
    metis_tac[supportedExprsTheory.supported_expr_def] >>
  qpat_x_assum `intcall_expr_producer _ _` mp_tac >>
  rewrite_tac[intcall_expr_producer_def] >> strip_tac >>
  first_x_assum drule_all >> disch_tac >>
  irule gas_outcome_post_mono >> goal_assum (drule_at Any) >>
  BETA_TAC >> rpt strip_tac >>
  drule_all intcall_vv_post_intro >> disch_tac >>
  drule supported_pure_expr_effect_free >> disch_tac >>
  qexists `tv` >> conj_tac >- simp[] >>
  conj_tac >- (qexists `b` >> simp[]) >>
  asm_rewrite_tac[]
QED

(* The invariant uses the original source state only for scope domains and
   the composed continuation; the deferred values live at the current state. *)
val prefix_inv = ``\fp ce env es a s d de dv dr (rest:expr list) ee b u.
  ^deferred_list fp ce de dv dr b ee u /\
  intcall_expr_cont fp ce env es a s ee b u /\
  a.cs_next_id <= b.cs_next_id /\ a.cs_next_var <= b.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ fn_has_code b d fp.jc_func``;

Theorem intcall_deferred_suffix:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  fn_inst_ids_distinct fp.jc_func /\ intcall_expr_res fp ce env es a s /\
  (!e. MEM e whole ==>
    intcall_expr_producer fp e /\ supported_pure_expr fp.jc_tops e /\
    expr_body_pre ce fp.jc_cx env e es /\
    calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) /\
  whole = doneE ++ todo /\
  ^prefix_inv fp ce env es a s d doneE doneV doneR todo ee b t /\
  compile_multi_vvs compile_expr ce todo b = (vvs,d) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr_results fp.jc_cx todo) (ee,t)
    (\res ef u. ?rs. res = INL rs /\
      ^prefix_inv fp ce env es a s d (doneE ++ todo) (doneV ++ vvs)
        (doneR ++ rs) [] ef d u)
    (\res ef r. ?ex. res = INR ex /\ expr_exit (INR ex) r)
Proof
  strip_tac >>
  BETA_TAC >>
  match_mp_tac (BETA_RULE (Q.ISPEC `\ex (ef:evaluation_state) r. expr_exit (INR ex) r`
    (Q.GEN `X` (Q.ISPEC `^prefix_inv fp ce env es a s d`
      (Q.GEN `P` (Q.ISPEC `compile_expr`
        (Q.GEN `cfn` intcall_compile_multi_vvs_suffix))))))) >>
  qexists `b` >>
  conj_tac >- suspend "reset" >>
  conj_tac >- suspend "child" >>
  rule_assum_tac BETA_RULE >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume intcall_deferred_suffix[reset]:
  BETA_TAC >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  conj_tac >- fs[intcall_expr_cont_def] >>
  pure_rewrite_tac[BETA_RULE intcall_deferred_list_gas_obs,
    intcall_expr_cont_final_gas] >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[]
QED

Resume intcall_deferred_suffix[child]:
  BETA_TAC >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 assume_tac strip_assume_tac) strip_assume_tac)) >>
  rename [`compile_expr ce (expr_type child) child c = (vv,cnext)`,
          `intcall_expr_cont fp ce env es a s live c v`] >>
  `MEM child whole` by simp[listTheory.MEM_APPEND] >>
  qpat_x_assum `!e. MEM e whole ==> _` (qspec_then `child` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all intcall_traverse_code_split >> strip_tac >>
  `intcall_expr_res fp ce env live c v /\ ~v.vs_halted /\
   v.vs_current_bb = c.cs_current_bb /\
   v.vs_inst_idx = LENGTH c.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `expr_body_pre ce fp.jc_cx env child live` by
    (irule expr_body_pre_state_transport >>
     conj_tac >- fs[intcall_expr_res_def] >>
     qexists `es` >> first_assum ACCEPT_TAC) >>
  drule_all intcall_traverse_child_admissible >> disch_tac >>
  drule_all (BETA_RULE intcall_deferred_child_run) >> disch_tac >>
  qpat_x_assum `LENGTH de = _ /\ _` strip_assume_tac >>
  drule_all (BETA_RULE intcall_counted_prefix_child) >> disch_tac >>
  irule exprSimSubscriptMapTheory.gas_outcome_conseq >>
  goal_assum (drule_at Any) >> conj_tac
  >- (BETA_TAC >> rpt gen_tac >> Cases_on `res` >>
      simp[NoAsms, stmtSimPropsTheory.expr_exit_INR_type]) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  qexists `r` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[] >> metis_tac[]
QED

Finalise intcall_deferred_suffix
