(* Reinterpret a stack result without extending its compile interval.
   The source changes only by wrapping successful values. *)
Theory entryCreateBuiltinStack
Ancestors
  entryCreateFocusSpec entryCreateCompletedCut entryCreateBodyCut
  bodyFullExprGeneric exprSimStack exprSimFullBundleProps exprSimDefs
  s1PrefixDefs gasStorage gasExemptCert gasExplicitSites gasContext
  loweringPosts bodyPtrDefs context exprLowering compileEnv vyperInterpreter vyperState

Theorem stack_value_vv_pre[local]:
  (!st tv ee. eval_expr cx e st = (INL tv,ee) ==> ?v. tv = Value v) /\
  expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,b,sha,shb,StackValue ann op,s0,G0,tn0) ==>
  expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,b,sha,shb,op,s0,G0,tn0)
Proof
  simp[expr_vv_sim_full_pre_def, expr_sim_full_pre_def] >> strip_tac >>
  simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  metis_tac[eval_expr_force_admissible]
QED

Theorem stack_value_vv_post[local]:
  compile_expr ce ty e a = (StackValue ann op,b) /\
  (~is_word_type (post_value_type ce e) ==>
    !tvt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvt ==>
          type_memory_size tvt = 0) /\
  expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,b,s0,op,G0,tn0) H res ee G tn t ==>
  create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,b,s0,StackValue ann op,G0,tn0)
    H (case res of INL v => INL (Value v) | INR ex => INR ex) ee G tn t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def] >> strip_tac >>
  drule_all expr_stack_value_post >> strip_tac >>
  simp[create_operand_vv_post_def, ptr_vv_ok_def, vv_location_def,
       read_result_def, return_def] >> metis_tac[]
QED

Theorem stack_value_scoped_source[local]:
  (!st tv ee. eval_expr cx e st = (INL tv,ee) ==> ?v. tv = Value v) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q R /\
  (!H res ee G tn t. Q H res ee G tn t ==>
     Q' H (case res of INL v => INL (Value v) | INR ex => INR ex) ee G tn t) /\
  (!H res ee gt r. R H res ee gt r ==>
     R' H (case res of INL v => INL (Value v) | INR ex => INR ex) ee gt r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (eval_expr cx e) (es,s0,G0,tn0) Q' R'
Proof
  strip_tac >>
  drule eval_expr_force_value >> strip_tac >>
  `!st. SND (eval_expr cx e st) = SND (bind (eval_expr cx e) (read_result cx) st)` by
    (gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) st` >> res_tac >> simp[]) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> fs[gas_bad_storage_at_def] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                    `ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> res_tac >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  drule eval_expr_force_ignore >> disch_then (fn th => fs[th]) >> metis_tac[]
QED

Theorem stack_value_cut_source[local]:
  (!st tv ee. eval_expr cx e st = (INL tv,ee) ==> ?v. tv = Value v) /\
  create_operand_cut a b E C f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0) ==>
  create_operand_cut a b E C f tops cx st0 (eval_expr cx e) (es,s0)
Proof
  rw[create_operand_cut_def, create_body_cut_def] >>
  qmatch_asmsub_abbrev_tac `eval_expr cx e input` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) input` >>
  rename1 `bind _ _ input = (raw,mid)` >>
  drule_all eval_expr_force_value >> strip_tac >> gvs[] >>
  qpat_x_assum `!p d k before hit after. _ ==> _` drule >>
  simp[create_body_cut_def] >> strip_tac >>
  `create_cut_failure tops raw` by (first_x_assum irule >> metis_tac[]) >>
  Cases_on `raw` >> gvs[create_cut_failure_def]
QED

Theorem create_builtin_stack_vv_at:
  expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es
    (st0,a,b,sha,shb,StackValue ann op,s0,G0,tn0) /\
  (!st tv ee. eval_expr cx e st = (INL tv,ee) ==> ?v. tv = Value v) /\
  (~is_word_type (post_value_type ce e) ==>
    !tvt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tvt ==>
          type_memory_size tvt = 0) /\
  (expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty e es
     (st0,a,b,sha,shb,op,s0,G0,tn0) ==>
   scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st0 a b
     (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (expr_sim_full_post (DF,lo,d,C,f) ce cx e (es,a,b,s0,op,G0,tn0))
     (create_operand_exit_post C cx) /\
   create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0
     (bind (eval_expr cx e) (read_result cx)) (es,s0)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st0 a b
    (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t.
       create_operand_vv_post (DF,lo,d,C,f) ce cx e (es,a,b,s0,StackValue ann op,G0,tn0)
         H res ee G tn t /\
       t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts)
    (create_operand_exit_post C cx) /\
  create_operand_cut a b (gas_explicit_sites C shC) C f tops cx st0 (eval_expr cx e) (es,s0)
Proof
  strip_tac >> drule_all stack_value_vv_pre >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  reverse conj_tac
  >- (irule stack_value_cut_source >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `compile_expr ce ty e a = (StackValue ann op,b)` by fs[expr_vv_sim_full_pre_def] >>
  irule stack_value_scoped_source >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac
  >- (strip_tac >> irule stack_value_vv_post >>
      first_assum (irule_at Any) >> metis_tac[]) >>
  simp[create_operand_exit_post_def, expr_exit_success_map] >>
  Cases_on `res` >> simp[halt_exit_def]
QED
