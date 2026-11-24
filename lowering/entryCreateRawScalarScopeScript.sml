(* RawCreate evaluates the amount, then at most one salt. The prepared
   byte window stays in the caller's frame until the dispatch continuation. *)
Theory entryCreateRawScalarScope
Ancestors
  bodyFullCreateHeld entryCreateFocusSpec
  fragGasOriginPtr fragGasOrigin fragGasMode gasSummaryCompose gasSummary
  exprSimWordArgs exprSimSend vyperStorageTrace vyperStorageFootprint
  gasStorage vyperTypeSystem vyperState vyperInterpreter vyperCreate
  builtinCreate exprLowering exprLoweringProps compileEnv loweringPosts finite_map list option pair

Theorem raw_scalar_source_nil[local]:
  bind (eval_exprs cx [amount]) (\vs. next (HD vs) NONE) =
    bind (bind (eval_expr cx amount) (read_result cx)) (\av. next av NONE)
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  once_rewrite_tac[eval_exprs_cons_action] >> simp[bind_assoc,bind_return]
QED

Theorem raw_scalar_source_cons[local]:
  bind (eval_exprs cx [amount;salt]) (\vs. next (HD vs) (SOME (EL 1 vs))) =
    bind (bind (eval_expr cx amount) (read_result cx))
      (\av. bind (bind (eval_expr cx salt) (read_result cx))
                  (\sv. next av (SOME sv)))
Proof
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  ntac 2 (once_rewrite_tac[eval_exprs_cons_action]) >>
  simp[bind_assoc,bind_return]
QED

(* The readings for the list replay come from the actual concatenated
   path: the second child reads from the amount's endpoint gas history. *)
Theorem raw_scalar_replay_salted[local]:
  gas_path ctx func s (LENGTH ma) (OK m) /\
  (!tail. bind (eval_expr cx amount) (read_result cx)
     (es with gas_obs := gas_explicit ma s.vs_gas_readings ++ tail) =
     (INL av,em with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx salt) (read_result cx)
     (em with gas_obs := gas_explicit ms m.vs_gas_readings ++ tail) =
     (INL sv,ee with gas_obs := tail)) ==>
  !tail. eval_exprs cx [amount;salt]
    (es with gas_obs := gas_explicit (ma ++ ms) s.vs_gas_readings ++ tail) =
    (INL [av;sv],ee with gas_obs := tail)
Proof
  strip_tac >> drule gas_explicit_append_path >> disch_then (qspec_then `ms` SUBST1_TAC) >>
  irule create_eval_exprs_cons_replay >> qexists_tac `em` >> simp[] >>
  once_rewrite_tac[eval_exprs_cons_action] >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
  simp[GSYM bind_assoc,bind_def,return_def]
QED

(* The normal half of the common scalar handoff, at its chosen marks. The
   scope and exception cases belong to the binder, not to this packet. *)
Definition raw_scalar_return_def:
  raw_scalar_return (DF,lo,d,E,ctx,func,PG) tops ce cx env st0 e
    (sa,op,es,s,G,tn) sb (marks,v,ee,t,G1,tn1) <=>
    storage_trace_domain cx st0 ee.storage_trace /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func ce cx e es sa sb s ee v op t /\
      ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t /\
      valid_horizon cx st0 H es.storage_trace /\
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ptr_val_ok cx (post_value_type ce e) v op G1 tn1 t /\
    ghost_kept_at lo ce es sa G tn s G1 tn1 /\ return_buf_frame d ce sb t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv ce cx env ee /\ expr_result_typed env e (Value v)
End

Definition raw_scalar_dispatch_post_def:
  raw_scalar_dispatch_post (DF,lo,d,E,ctx,func,PG) ce cx env st0 amount salts
    (sa,y,es,s,G,tn) (sb,sop) (marks,av,sv,yw,sw,ee,t,G1,tn1) <=>
    dest_NumV av = SOME (w2n yw) /\ dest_optional_salt sv = SOME sw /\
    (!tail. eval_exprs cx (amount::salts)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL (av::(case sv of NONE => [] | SOME v => [v])),ee with gas_obs := tail)) /\
    eval_operand y t = SOME yw /\ op_taint tn1 y = {} /\
    OPTREL (\op w. eval_operand op t = SOME w /\ op_taint tn1 op = {}) sop sw /\
    (!x. y = Var x \/ sop = SOME (Var x) ==> not_fresh_at sb x) /\
    wb_frame ce es ee sa s t /\ ghost_kept_at lo ce es sa G tn s G1 tn1 /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ expr_sim_inv ce cx env ee /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_history func t /\
    return_buf_frame d ce sb t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1))
End

Theorem raw_scalar_return_word[local]:
  raw_scalar_return (DF,lo,d,E,ctx,func,PG) tops ce cx env st0 e
    (sa,op,es,s,G,tn) sb (marks,v,ee,t,G1,tn1) /\
  expr_body_pre ce cx env e es /\ expr_type e = BaseT bt /\ is_word_type (BaseT bt) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sb) ==>
  value_has_type (BaseTV bt) v /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  op_taint tn1 op = {} /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l) /\
  wb_frame ce es ee sa s t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t)
Proof
  rewrite_tac[raw_scalar_return_def] >> strip_tac >>
  irule create_word_cut_frame_facts >>
  simp[] >> qexistsl_tac [`e`,`env`] >> simp[] >> rpt strip_tac >> res_tac
QED

Theorem raw_scalar_amount_dispatch[local]:
  raw_scalar_return (DF,lo,d,E,ctx,func,PG) tops ce cx env st0 amount
    (sa,y,es,s,G,tn) sm (marks,av,em,m,Gm,tm) /\
  expr_body_pre ce cx env amount es /\ expr_type amount = BaseT (UintT 256) /\
  lower_value compile_expr ce (expr_type amount) amount sa = (y,sm) ==>
  ?yw. raw_scalar_dispatch_post (DF,lo,d,E,ctx,func,PG) ce cx env st0 amount []
    (sa,y,es,s,G,tn) (sm,NONE) (marks,av,NONE,yw,NONE,em,m,Gm,tm)
Proof
  strip_tac >>
  `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  drule_all raw_scalar_return_word >> strip_tac >> fs[raw_scalar_return_def] >>
  qexists_tac `typed_val_to_w256 (BaseTV (UintT 256)) av` >>
  simp[raw_scalar_dispatch_post_def,dest_optional_salt_def,OPTREL_def,uint256_typed_dest] >>
  `MAP FDOM es.scopes = MAP FDOM em.scopes` by fs[wb_frame_def,locals_kept_def] >>
  conj_tac
  >- (once_rewrite_tac[eval_exprs_cons_action] >>
      `eval_exprs cx [] = return []` by simp[FUN_EQ_THM,eval_exprs_nil,return_def] >>
      simp[GSYM bind_assoc,bind_def,return_def]) >>
  simp[] >> rpt strip_tac >> res_tac
QED

Theorem raw_scalar_salted_dispatch[local]:
  raw_scalar_return (DF,lo,d,E,ctx,func,PG) tops ce cx env st0 amount
    (sa,y,es,s,G,tn) sm (ma,av,em,m,Gm,tm) /\
  raw_scalar_return (DF,lo,d,E,ctx,func,PG) tops ce cx env st0 salt
    (sm,sop,em,m,Gm,tm) sb (ms,sv,ee,t,G1,tn1) /\
  expr_body_pre ce cx env amount es /\ expr_type amount = BaseT (UintT 256) /\
  expr_body_pre ce cx env salt em /\ expr_type salt = BaseT (BytesT (Fixed 32)) /\
  lower_value compile_expr ce (expr_type amount) amount sa = (y,sm) /\
  lower_value compile_expr ce (expr_type salt) salt sm = (sop,sb) /\
  local_ptrs_reserved ce sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s) ==>
  ?yw sw. raw_scalar_dispatch_post (DF,lo,d,E,ctx,func,PG) ce cx env st0 amount [salt]
    (sa,y,es,s,G,tn) (sb,SOME sop) (ma ++ ms,av,SOME sv,yw,SOME sw,ee,t,G1,tn1)
Proof
  strip_tac >>
  `is_word_type (BaseT (UintT 256)) /\ is_word_type (BaseT (BytesT (Fixed 32)))`
    by simp[is_word_type_def] >>
  qpat_assum `raw_scalar_return _ _ _ _ _ _ amount _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) raw_scalar_return_word) >>
  qpat_assum `raw_scalar_return _ _ _ _ _ _ salt _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) raw_scalar_return_word) >>
  fs[raw_scalar_return_def] >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace`
    by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) es.storage_trace`
    by metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon em.storage_trace) ctx func ce cx es s` by simp[] >>
  `gas_path ctx func s (LENGTH ma) (OK m)` by
    (qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> expr_post _ _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule_then (irule o MATCH_MP gas_marked_path_exec) gas_origin_path_erase) >>
  `ci_mono sa sm /\ ci_mono sm sb` by metis_tac[ci_mono_lower_value_compile_expr,SND] >>
  qpat_assum `eval_operand y m = SOME _`
    (mp_then Any (drule_all_then strip_assume_tac) create_cut_frames_keep_operand) >>
  `!x. y = Var x ==> not_fresh_at sb x` by
    metis_tac[ci_mono_def,loweringShapeDefsTheory.not_fresh_at_mono] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by fs[wb_frame_def,locals_kept_def] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`typed_val_to_w256 (BaseTV (UintT 256)) av`,
                `typed_val_to_w256 (BaseTV (BytesT (Fixed 32))) sv`] >>
  simp[raw_scalar_dispatch_post_def,dest_optional_salt_def,OPTREL_def,
       uint256_typed_dest,create_salt_word] >>
  conj_tac >- (irule raw_scalar_replay_salted >> qexistsl_tac [`ctx`,`em`,`func`,`m`] >> simp[]) >>
  conj_tac >- (rpt strip_tac >> res_tac) >>
  conj_tac >- (rpt strip_tac >> res_tac) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post _ _ _ _ _ salt _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> expr_post _ _ _ _ _ amount _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  TRY (first_assum ACCEPT_TAC) >>
  irule gas_origin_ptr_path_append >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* The two continuation laws are the common scalar scoped bind specialized
   to the installed amount and salt cuts. They quantify over continuations,
   not over successful runs: either child can focus or terminate. *)
Theorem raw_create_scalar_scoped_suffix:
  expr_body_pre ce cx env amount es /\ expr_type amount = BaseT (UintT 256) /\
  lower_value compile_expr ce (expr_type amount) amount sa = (y,sm) /\
  (if salted then ?salt. salts = [salt] /\ expr_type salt = BaseT (BytesT (Fixed 32))
   else salts = []) /\
  compile_create_salt compile_expr ce (if salted then SOME (HD salts) else NONE) sm = (sop,sb) /\
  (!salt em. MEM salt salts /\ expr_sim_inv ce cx env em ==> expr_body_pre ce cx env salt em) /\
  local_ptrs_reserved ce sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s) /\
  (!k. (!av. storage_trace_frame (k av)) /\
    (!ma av em m Gm tm.
      raw_scalar_return (DF,lo,d,gas_explicit_sites ctx hctx,ctx,func,PG)
        tops ce cx env st0 amount (sa,y,es,s,G,tn) sm (ma,av,em,m,Gm,tm) ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
        tops cx st0 sm end_cut (k av) (em,m,Gm,tm) Q (create_operand_exit_post ctx cx)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      tops cx st0 sa end_cut (bind (bind (eval_expr cx amount) (read_result cx)) k)
      (es,s,G,tn) Q (create_operand_exit_post ctx cx)) /\
  (!salt pop ma av em m Gm tm k.
    salted /\ salts = [salt] /\ sop = SOME pop /\
    raw_scalar_return (DF,lo,d,gas_explicit_sites ctx hctx,ctx,func,PG)
      tops ce cx env st0 amount (sa,y,es,s,G,tn) sm (ma,av,em,m,Gm,tm) /\
    (!sv. storage_trace_frame (k sv)) /\
    (!ms sv ee t G1 tn1.
      raw_scalar_return (DF,lo,d,gas_explicit_sites ctx hctx,ctx,func,PG)
        tops ce cx env st0 salt (sm,pop,em,m,Gm,tm) sb (ms,sv,ee,t,G1,tn1) ==>
      scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
        tops cx st0 sb end_cut (k sv) (ee,t,G1,tn1) Q (create_operand_exit_post ctx cx)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      tops cx st0 sm end_cut (bind (bind (eval_expr cx salt) (read_result cx)) k)
      (em,m,Gm,tm) Q (create_operand_exit_post ctx cx)) /\
  (!av sv. storage_trace_frame (next av sv)) /\
  (!marks av sv yw sw ee t G1 tn1.
    IS_SOME sv = salted /\
    raw_scalar_dispatch_post (DF,lo,d,gas_explicit_sites ctx hctx,ctx,func,PG)
      ce cx env st0 amount salts (sa,y,es,s,G,tn) (sb,sop)
      (marks,av,sv,yw,sw,ee,t,G1,tn1) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
      tops cx st0 sb end_cut (next av sv) (ee,t,G1,tn1) Q (create_operand_exit_post ctx cx)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
    tops cx st0 sa end_cut
    (bind (eval_exprs cx (amount::salts)) (\vs. next (HD vs) (if salted then SOME (EL 1 vs) else NONE)))
    (es,s,G,tn) Q (create_operand_exit_post ctx cx)
Proof
  strip_tac >> Cases_on `salted` >> gvs[compile_create_salt_def,comp_return_def]
  >- suspend "salted" >>
  rewrite_tac[raw_scalar_source_nil] >>
  qpat_assum `!k. _ ==> scoped_operand_outcome _ _ _ _ sa end_cut _ _ _ _` irule >>
  simp[] >> rpt strip_tac >>
  `lower_value compile_expr ce (expr_type amount) amount sa = (y,sb)` by simp[] >>
  drule_all raw_scalar_amount_dispatch >> strip_tac >>
  qpat_assum `!marks av yw sw ee t G1 tn1. _ ==> _` (drule_then ACCEPT_TAC)
QED

Resume raw_create_scalar_scoped_suffix[salted]:
  rename1 `expr_type salt = BaseT (BytesT (Fixed 32))` >>
  Cases_on `lower_value compile_expr ce (expr_type salt) salt sm` >>
  gvs[comp_bind_def,comp_return_def] >>
  rewrite_tac[raw_scalar_source_cons] >>
  qpat_assum `!k. _ ==> scoped_operand_outcome _ _ _ _ sa end_cut _ _ _ _` irule >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  rpt strip_tac >>
  qpat_assum `!ma av em m Gm tm k. _ ==> scoped_operand_outcome _ _ _ _ sm end_cut _ _ _ _` irule >>
  simp[] >>
  reverse conj_tac >- (qexistsl_tac [`av`,`ma`] >> simp[]) >>
  rpt strip_tac >>
  `expr_body_pre ce cx env salt em` by
    (qpat_assum `!em. expr_sim_inv ce cx env em ==> expr_body_pre ce cx env salt em` irule >>
     qpat_assum `raw_scalar_return _ _ _ _ _ _ amount _ _ _`
       (strip_assume_tac o REWRITE_RULE[raw_scalar_return_def]) >>
     first_assum ACCEPT_TAC) >>
  `lower_value compile_expr ce (expr_type amount) amount sa = (y,sm) /\
   lower_value compile_expr ce (expr_type salt) salt sm = (q,r)` by simp[] >>
  drule_all raw_scalar_salted_dispatch >> strip_tac >>
  qpat_assum `!marks av sv yw sw ee t G1 tn1. _ ==> _` irule >>
  simp[] >> qexistsl_tac [`ma ++ ms`,`SOME sw`,`yw`] >> simp[]
QED

Finalise raw_create_scalar_scoped_suffix
