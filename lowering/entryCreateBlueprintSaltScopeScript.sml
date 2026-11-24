(* The optional blueprint salt is a scoped scalar continuation.  The
   amount and offset producers remain hypotheses of the enclosing join. *)
Theory entryCreateBlueprintSaltScope
Ancestors
  entryCreateSelectedSalt entryCreateBlueprintReadCut createSizeBlueprintKeywordReplay
  bodyFullPreds vyperState createSizeCopyReplay exprSimWordArgs
  exprBodyPreProps vyperTypeExprSoundness vyperValue vyperTyping vyperCreate

(* At the normal amount return, NONE preserves the amount cursor and SOME
   evaluates exactly one fixed-width salt.  This is the source/ghost handoff
   consumed by the offset continuation; it deliberately does not select an
   amount or offset producer. *)
Theorem blueprint_salt_scoped_bind:
  (hs ==> expr_body_pre ce cx env salt p /\
      expr_type salt = BaseT (BytesT (Fixed 32)) /\
      (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
         ce cx (expr_type salt) salt p (st0,ca,cb,sca,scb,op,u,G,tn) ==>
       gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
         tops cx st0 ca cb (bind (eval_expr cx salt) (read_result cx)) (p,u,G,tn)
         (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx salt (p,ca,cb,u,op,G,tn)))) /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_sim_inv ce cx env p /\ body_const_cells_agree [(NONE,tops)] cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt ca = (op,cb) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt)
        (gas_shadow_expr salt) sca = (op,scb) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
      create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
      t.vs_current_bb = cb.cs_current_bb /\
      t.vs_inst_idx = LENGTH cb.cs_current_insts
   else cb = ca /\ scb = sca /\ t = u /\ chunk = []) /\
  (!vs. storage_trace_frame (k vs)) /\
  bind (eval_exprs cx (if hs then [salt] else [])) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?svs q G' tn'.
    eval_exprs cx (if hs then [salt] else []) p = (INL svs,q) /\
    k svs q = (res,out) /\
    (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    body_const_cells_agree [(NONE,tops)] cx env q /\
    expr_sim_inv ce cx env q /\ ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
    return_buf_frame d ce cb t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
Proof
  reverse (Cases_on `hs`) >> simp[cj 49 vyperInterpreterTheory.evaluate_def, return_def, bind_return] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (disj2_tac >> qexistsl [`G`,`tn`] >> gvs[] >> first_assum ACCEPT_TAC) >>
  `bind (bind (eval_expr cx salt) (read_result cx)) (\v. k [v]) p = (res,out)` by
    fs[create_copy_source_cons, cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  `!v. storage_trace_frame ((\v. k [v]) v)` by simp[] >>
  drule_all blueprint_read_at_cut_from_replay >> strip_tac >- metis_tac[] >>
  `body_const_cells_agree [(NONE,tops)] cx env q` by
    (irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at Any) >> drule expr_body_pre_static_facts >> simp[]) >>
  `?w. dest_create_salt v = SOME w` by
    (qpat_assum `expr_type salt = _` (fn th =>
       qpat_assum `value_runtime_typed _ _ v` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `v` >> simp[value_runtime_typed_def, evaluate_type_def,
       value_has_type_def, dest_create_salt_def, dest_BytesV_def]) >>
  `eval_exprs cx [salt] p = (INL [v],q)` by
    (irule blueprint_eval_join_cons >> metis_tac[eval_exprs_nil]) >>
  disj2_tac >> qexistsl [`[v]`,`q`,`G'`,`tn'`] >> fs[] >> first_assum ACCEPT_TAC
QED
