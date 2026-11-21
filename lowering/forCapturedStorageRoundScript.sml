Theory forCapturedStorageRound
Ancestors
  forCapturedStorageLive bodyFullForStorage bodyFullPreds bodyFullForFrame
  loweringStateRelDefs stmtSimDefs bodyPtrDefs allocaHistory ptrDiscipline
  compileEnv vyperStorageFootprint vyperState fragExec venomState venomInst
  fragGasOriginPtr gasContext words finite_map list arithmetic
  exprLoweringProps bodyFullGhostFrame bodyFullShared stmtSimProps bodyMemoryDefs
  typedCopyOriginPtrBase stmtSimForArrayLoop bodySimFull

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

(* The increment has only two output registers. The body has already returned
   to the outer source scope, so neither the subregion witness nor its trace
   prefix changes along this edge. *)
Theorem for_captured_storage_increment_post[local]:
  for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
    (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
    (lvo,idx,incr) (p,dst,nb,sd) (H,k,a::rs,ee,G,tn,s) /\
  k < len /\ body_stmts_full_ok cx stmts /\
  local_ptrs_reserved c0 sa0 /\ ~not_fresh_at sa0 idx /\ ~not_fresh_at sa0 out /\
  (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  p <> idx /\ p <> out /\
  (!x. lvo = Var x ==> x <> idx /\ x <> out) /\
  (!x. bop = Var x ==> x <> idx /\ x <> out) /\
  t = jump_to cond (update_var idx (n2w (SUC k)) (update_var out (n2w (SUC k)) s)) /\
  tf = (tn with t_var := (tn.t_var |+ (out,{})) |+ (idx,{})) /\
  lookup_var idx t = SOME (n2w (SUC k)) /\ FLOOKUP Gf idx = NONE /\
  op_taint tf (Var idx) = {} /\
  (!x. x <> idx /\ x <> out ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) ==>
  for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
    (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
    (lvo,idx,cond) (p,dst,nb,sd) (H,SUC k,rs,ee,Gf,tf,t)
Proof
  rewrite_tac[for_captured_storage_live_def] >> strip_tac >>
  `!x. not_fresh_at sa0 x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. x <> idx /\ x <> out ==> _` irule >> metis_tac[]) >>
  `not_local_ptr c0 ee.scopes idx /\ not_local_ptr c0 ee.scopes out` by
    metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
   t.vs_labels = s.vs_labels /\ t.vs_memory = s.vs_memory /\
   t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
   ~t.vs_halted /\ tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
   tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    (qpat_assum `t = jump_to _ _` (fn th => simp[th,jump_to_def,update_var_def]) >>
     qpat_assum `tf = _` (fn th => simp[th])) >>
  `stmt_state_rel H ctx func c0 cx ee t` by
    (qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac[th]) >>
     simp[stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule stmt_state_rel_update_var >> simp[]) >>
  `ghost_inv_at (DF H) lo d c0 cx ee Gf tf t` by
    (irule ghost_inv_at_exterior_frame >> qexistsl [`G`,`ee`,`s`,`sa0`,`tn`] >> simp[]) >>
  suspend "out_frames"
QED

Resume for_captured_storage_increment_post[out_frames]:
  `return_buf_frame d c0 sa0 t` by
    (irule return_buf_frame_frame >> qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
  `ret_pc_ok c0 sa0 t` by
    (irule ret_pc_ok_frame >> qexistsl [`c0`,`s`,`sa0`] >> simp[] >> metis_tac[]) >>
  `!name b sz. local_region c0 ee.scopes t name b sz <=> local_region c0 ee.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >> metis_tac[not_local_ptr_def]) >>
  `return_buf_sep d c0 ee t` by
    (irule return_buf_sep_transport >>
     conj_tac
     >- (map_every qx_gen_tac [`bw`,`cap`] >> disch_tac >>
         qpat_assum `d = SOME (bw,cap)` SUBST_ALL_TAC >>
         qpat_assum `return_buf_sep (SOME (bw,cap)) c0 ee s`
           (mp_tac o CONJUNCT1 o REWRITE_RULE [return_buf_sep_def]) >>
         rewrite_tac[allocas_from_def] >>
         qpat_assum `t.vs_allocas = s.vs_allocas` SUBST1_TAC >> simp[NoAsms]) >>
     qexistsl [`c0`,`ee`,`s`] >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!n b sz. local_region c0 ee.scopes t n b sz <=> _`
       (rewrite_tac o single)) >>
  `alloca_frame c0 e0 sa0 s0 c0 ee t` by
    (qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac[th]) >>
     irule alloca_frame_same_state >>
     qexists `update_var idx (n2w (SUC k)) (update_var out (n2w (SUC k)) s)` >>
     simp[jump_to_def] >>
     irule alloca_frame_update_var >> simp[] >> irule alloca_frame_update_var >> simp[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac[th]) >>
     simp[allocas_below_fmp_def,jump_to_def,update_var_def] >> metis_tac[allocas_below_fmp_def]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists `s` >> simp[]) >>
  suspend "finish"
QED

Resume for_captured_storage_increment_post[finish]:
  qpat_x_assum `t = jump_to _ _` kall_tac >> qpat_x_assum `tf = _` kall_tac >>
  `eval_operand lvo t = SOME (n2w len) /\ op_taint tf lvo = {} /\ op_prov Gf lvo = NONE` by
    (Cases_on `lvo` >> fs[IgnAsm `len = LENGTH vs`, eval_operand_def, op_taint_def, op_prov_def] >>
     metis_tac[]) >>
  `eval_operand bop t = SOME slot /\ op_taint tf bop = {}` by
    (Cases_on `bop` >> fs[IgnAsm `len = LENGTH vs`, eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `ptr_covers Gf tf p t nb` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`G`,`s`,`tn`] >> simp[]) >>
  `rs = DROP (SUC k) vs` by
    (qpat_assum `a::rs = DROP k vs` (mp_tac o MATCH_MP DROP_EQ_CONS o SYM) >>
     simp[NoAsms]) >>
  simp[IgnAsm `len = LENGTH vs`, IgnAsm `vs = GENLIST _ _`] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  TRY (qexists `extra` >> first_assum ACCEPT_TAC) >>
  TRY (qexistsl [`off`,`root`,`path`,`delta`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  TRY (qpat_assum `!n b sz. local_region c0 ee.scopes s n b sz ==> _` drule >> decide_tac) >>
  metis_tac[]
QED

Finalise for_captured_storage_increment_post

Theorem for_captured_storage_backedge[local]:
  emit_op ADD [Var idx; Lit 1w] si = (Var out,sj) /\
  emit_inst ASSIGN [Var out] [idx] sj = ((),sk) /\
  emit_inst JMP [Label cond] [] sk = ((),sl) /\ fn_has_code si sl func /\
  not_fresh_at si idx /\ si.cs_current_insts = [] /\
  local_ptrs_reserved c0 sa0 /\ ~not_fresh_at sa0 idx /\ ~not_fresh_at sa0 out /\
  (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  p <> idx /\ p <> out /\
  (!x. lvo = Var x ==> x <> idx /\ x <> out) /\
  (!x. bop = Var x ==> x <> idx /\ x <> out) /\
  k < len /\ body_stmts_full_ok cx stmts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
      (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
      (lvo,idx,si.cs_current_bb) (p,dst,nb,sd) (H,k,a::rs,ee,G,tn,s)) ==>
  ?t Gf tf. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
    for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
      (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
      (lvo,idx,cond) (p,dst,nb,sd) (H,SUC k,rs,ee,Gf,tf,t)
Proof
  strip_tac >>
  qexistsl [`jump_to cond (update_var idx (n2w (SUC k)) (update_var out (n2w (SUC k)) s))`,
            `DRESTRICT (DRESTRICT G (COMPL {out})) (COMPL {idx})`,
            `tn with t_var := (tn.t_var |+ (out,{})) |+ (idx,{})`] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> disch_tac >>
  qpat_assum `for_captured_storage_live _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_captured_storage_live_def]) >>
  `allocas_from lo s` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  `s.vs_inst_idx = LENGTH si.cs_current_insts` by simp[] >>
  drule_all typed_copy_origin_ptr_counter_backedge_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`DF H`] strip_assume_tac) >>
  qpat_x_assum `Var out = Var out'` (SUBST_ALL_TAC o SYM o SRULE []) >>
  qpat_assum `t = jump_to _ _` (fn th => pure_rewrite_tac [GSYM th, ADD1]) >>
  qpat_assum `Gf = DRESTRICT _ _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_assum `tnf = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule (REWRITE_RULE [ADD1] for_captured_storage_increment_post) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`G`,`a`,`si.cs_current_bb`,`out`,`s`,`tn`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
