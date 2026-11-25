(* Compose the two selected scalar operand outcomes before entering arithmetic. *)
Theory entryCreateBopWordScopedOperands
Ancestors
  entryCreateScopedBind entryCreateRawStageJoins entryCreateFocusSpec
  exprBopSimProps exprBopSimDefs exprSimDefs exprSimFullBundleProps s1PrefixDefs
  entryCreateCompletedCut exprSimHyps exprSimSource compileEnv loweringPosts
  gasExemptCert vyperStorageTrace vyperStorageFootprint vyperState

Theorem bop_scoped_exception_post[local]:
  (\H (res : value + exception) ee gt r.
     ?exc. res = INR exc /\ create_operand_exit_post ctx cx H (INR exc) ee gt r) =
  create_operand_exit_post ctx cx
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >>
  Cases_on `res` >- simp[create_operand_exit_post_def] >>
  rename1 `INR ex` >> Cases_on `ex` >> Cases_on `r` >>
  simp[create_operand_exit_post_def, halt_exit_def, expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Theorem bop_scoped_normalize[local]:
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m source (es,s,G,tn)
    P R ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m source (es,s,G,tn)
    (\H res mid G1 tn1 t. mid.gas_obs = [] /\ P H res mid G1 tn1 t) R
Proof
  rewrite_tac[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem bop_word_read_scoped_bind[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_layout a b /\ create_cut_code {} a m /\ create_cut_code {} m b /\
  fn_has_code a b f /\ create_operand_at a s /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn))
    (create_operand_exit_post ctx cx) /\
  (!marks v mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    create_operand_at m t /\ create_operand_full_scope a m E ctx f s marks (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn) H
        (INL v : value + exception) mid G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 m b (next v)
      (mid,t,G1,tn1) Q (create_operand_exit_post ctx cx)) /\
  (!v. storage_trace_frame (next v)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn) Q
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >> drule_all raw_create_scope_at_split >>
  disch_then (qspec_then `E` strip_assume_tac) >>
  drule_then assume_tac bop_scoped_normalize >>
  irule scoped_operand_bind_all_mixed >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,bop_scoped_exception_post] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_bind_value >>
     qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_error_value >>
     simp[ignore_bind_def]) >>
  qexistsl_tac
    [`\H res mid G1 tn1 t. mid.gas_obs = [] /\
       expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,m,s,op,G,tn) H res mid G1 tn1 t`, `m`] >>
  simp[bop_scoped_exception_post] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `mid.gas_obs = [] /\ ?v. res = INL v` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [expr_sim_full_post_def] >> strip_tac >> simp[] >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  qpat_assum `!marks v mid G1 tn1 t. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (simp[] >> qx_gen_tac `h` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (qspec_then `h` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[expr_sim_full_post_def])) >>
  disch_then ACCEPT_TAC
QED

Theorem bop_word_suffix_storage_frame[local]:
  storage_trace_frame (\ee. (bop_result cx ann bop tys v1 v2 ee,ee))
Proof
  simp[storage_trace_frame_def,bop_result_def]
QED

Theorem create_bop_word_scoped_operands:
  let exp = Builtin ann (Bop bop) [e1;e2] in
  let read = \e. bind (eval_expr cx e) (read_result cx) in
  let cont = \v1 v2 ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee) in
  let E = gas_explicit_sites ctx shadow_ctx in
  let params = (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) in
  let post = expr_sim_full_post (DF,lo,d,ctx,func) ce cx in
  let Q = post exp (es,sa,sb,s0,op,G0,tn0) in
  let R = create_operand_exit_post ctx cx in
  let out = scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 in
  let row = \e es a m s G tn x marks v mid G1 tn1 t.
    (!tail. read e (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    create_operand_at m t /\ create_operand_full_scope a m E ctx func s marks (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      post e (es,a,m,s,x,G,tn) H (INL v) mid G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)) in
  let left_row = row e1 es sa s1 s0 G0 tn0 x in
  let right_pre = \mid t G1 tn1. expr_sim_full_pre params ce cx (expr_type e1) e2 mid
    (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1) in
  let success = ?p tv q p' v' q'. eval_expr cx e1 p = (INL tv,q) /\
                         read_result cx tv p' = (INL v',q') in
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  body_inv (cx_tops cx) ctx ce cx /\ body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
  expr_body_pre ce cx env exp es /\
  expr_sim_full_pre params ce cx ty exp es (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
  lower_value compile_expr ce (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e1) (gas_shadow_expr e1)
    shadow_sa = (x,shadow_s1) /\
  gas_shadow_state s1 shadow_s1 /\ fn_has_code sa s1 func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\ fn_has_code s1 sb func /\
  create_layout sa sb /\ create_layout s1 sb /\
  create_cut_code {} sa s1 /\ create_cut_code {} s1 sb /\
  create_cut_code {} s1 s2 /\ create_cut_code {} s2 sb /\
  (expr_body_pre ce cx env e1 es /\
   expr_sim_full_pre params ce cx (expr_type e1) e1 es (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0) ==>
   out sa s1 (read e1) (es,s0,G0,tn0) (post e1 (es,sa,s1,s0,x,G0,tn0)) R) /\
  (!left v1 mid G1 tn1 t. left_row left v1 mid G1 tn1 t ==>
    success /\ expr_body_pre ce cx env e2 mid /\
    body_const_cells_agree [(NONE,cx_tops cx)] cx env mid /\ right_pre mid t G1 tn1) /\
  (!mid t G1 tn1. success /\ expr_body_pre ce cx env e2 mid /\
    body_const_cells_agree [(NONE,cx_tops cx)] cx env mid /\ right_pre mid t G1 tn1 ==>
    out s1 s2 (read e2) (mid,t,G1,tn1) (post e2 (mid,s1,s2,t,y,G1,tn1)) R) /\
  (!left v1 mid G1 tn1 t right v2 fin G2 tn2 u.
    left_row left v1 mid G1 tn1 t /\ row e2 mid s1 s2 t G1 tn1 y right v2 fin G2 tn2 u ==>
    out s2 sb (cont v1 v2) (fin,u,G2,tn2) Q R) ==>
  out sa sb (read exp) (es,s0,G0,tn0) Q R
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `expr_body_pre ce cx env e1 es` by (drule expr_body_pre_bop >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es`
    by metis_tac[expr_body_pre_gas_admissible] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx (expr_type e1) e1 es
    (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0)` by
    (qpat_assum `expr_sim_full_pre _ _ _ _ (Builtin _ _ _) _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
     rewrite_tac[expr_sim_full_pre_def] >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  `create_operand_at sa s0 /\ fn_has_code sa sb func /\ MEM func ctx.ctx_functions`
    by fs[expr_sim_full_pre_def,create_operand_at_def] >>
  qpat_assum `_ ==> scoped_operand_outcome _ _ _ _ sa s1 _ _ _ _`
    (drule_all_then assume_tac) >>
  pure_rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  irule bop_word_read_scoped_bind >>
  qpat_assum `scoped_operand_outcome _ _ _ _ sa s1 _ _ _ _` (irule_at Any) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,bop_word_suffix_storage_frame] >>
  qx_genl_tac [`left`,`v1`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  qpat_assum `!left v1 mid G1 tn1 t. _ ==> _ /\ expr_body_pre _ _ _ e2 _ /\ _`
    (qspecl_then [`left`,`v1`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >> strip_tac >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx
    st0 s1 s2 (bind (eval_expr cx e2) (read_result cx)) (mid,t,G1,tn1)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e2 (mid,s1,s2,t,y,G1,tn1))
    (create_operand_exit_post ctx cx)` by
    (first_x_assum irule >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  irule bop_word_read_scoped_bind >>
  qpat_assum `scoped_operand_outcome _ _ _ _ s1 s2 _ _ _ _` (irule_at Any) >>
  simp[bop_word_suffix_storage_frame] >>
  qx_genl_tac [`right`,`v2`,`fin`,`G2`,`tn2`,`u`] >> strip_tac >>
  qpat_assum `!left v1 mid G1 tn1 t right v2 fin G2 tn2 u. _`
    (qspecl_then [`left`,`v1`,`mid`,`G1`,`tn1`,`t`,`right`,`v2`,`fin`,`G2`,`tn2`,`u`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  disch_then ACCEPT_TAC
QED
