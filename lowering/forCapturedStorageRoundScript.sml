Theory forCapturedStorageRound
Ancestors
  forCapturedStorageLive bodyFullForStorage bodyFullPreds bodyFullForFrame
  loweringStateRelDefs stmtSimDefs bodyPtrDefs allocaHistory ptrDiscipline
  compileEnv vyperStorageFootprint vyperState fragExec venomState venomInst
  fragGasOriginPtr gasContext words finite_map list

Definition for_captured_storage_done_def:
  for_captured_storage_done (DF,lo,d,ctx,func,cx,c0,lctx,sb)
    (e0,sa0,s0,G0,tn0) H ee G tn t <=>
    (?c. stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
         ~block_is_terminated sb /\ c = c0 /\ cenv_top_ext c0 c ee.scopes /\
         stmt_state_rel H ctx func c cx ee t /\
         storage_well_formed_on cx ee (FST H) /\
         return_buf_frame d c sb t /\ return_buf_sep d c ee t /\
         ghost_inv_at (DF H) lo d c cx ee G tn t /\
         alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
         s0.vs_alloca_next <= t.vs_alloca_next /\
         (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
         (!x. not_fresh_at sa0 x ==> FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x)) /\
         alloca_frame c0 e0 sa0 s0 c ee t /\
         (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
           aid < sa0.cs_next_id /\
           (!name b n. local_region c0 e0.scopes s0 name b n ==>
             off + sz <= b \/ b + n <= off) /\
           off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem))
End

Theorem for_captured_storage_nil_full:
  local_ptrs_reserved c0 sa0 /\
  (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  ~not_fresh_at sa0 dv /\ sa0.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\ ~block_is_terminated sb /\
  lookup_block cond func.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME (mk_inst eid EQ [Var idx; lvo] [dv]) /\
  get_instruction bb 1 = SOME (mk_inst (eid+1) JNZ [Var dv; Label exit; Label bod] []) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    ?k. for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
      (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
      (lvo,idx,cond) (p,dst,nb,sd) (H,k,[],es,G,tn,s)) ==>
  ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    for_captured_storage_done (DF,lo,d,ctx,func,cx,c0,lctx,sb)
      (e0,sa0,s0,G0,tn0) H (es with gas_obs := []) G1 tn1 t
Proof
  strip_tac >> rewrite_tac[for_captured_storage_done_def] >>
  irule (BETA_RULE for_storage_array_nil_core) >>
  simp[] >> qexistsl [`bb`,`bod`,`cond`,`dv`,`eid`,`idx`,`len`,`lvo`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
  rewrite_tac[for_captured_storage_live_def] >> strip_tac >>
  `k = len` by
    (qpat_assum `[] = DROP k vs` (mp_tac o SYM) >>
     rewrite_tac[DROP_EQ_NIL] >> decide_tac) >>
  qpat_x_assum `k = len` SUBST_ALL_TAC >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
