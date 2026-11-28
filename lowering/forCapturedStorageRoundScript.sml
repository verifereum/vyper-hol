Theory forCapturedStorageRound
Ancestors
  bodyFullPredsMods[qualified]
  forCapturedStorageLive bodyFullForStorage bodyFullPreds bodyFullForFrame
  loweringStateRelDefs stmtSimDefs bodyPtrDefs allocaHistory ptrDiscipline
  compileEnv vyperStorageFootprint vyperState fragExec venomState venomInst
  fragGasOriginPtr gasContext words finite_map list arithmetic
  exprLoweringProps bodyFullGhostFrame bodyFullShared stmtSimProps bodyMemoryDefs
  typedCopyOriginPtrBase stmtSimForArrayLoop bodySimFull
  forCapturedStorageCons forStorageBodyLand forBodyLandOutcome gasOutcomeFull gasOutcomeFullCompose
  freshWrites loweringPosts stmtLowering bodyFullIfExpReach
  allocaSiteResource stateRelProj localPtrsProps bodyMemBopRestWordPath
  exprSimHypsDefs vyperTypeStatePreservation vyperStorageTrace vyperInterpreter
  bodySim gasExplicitSites bodyFullForExprCut

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
    for_array_loop_post (DF,lo,d,ctx,func) c0 cx lctx (e0,sa0,s0,G0,tn0)
      sb H (INL ()) (es with gas_obs := []) G1 tn1 t
Proof
  strip_tac >>
  simp[for_array_loop_post_def, AC CONJ_ASSOC CONJ_COMM] >>
  irule (SIMP_RULE (srw_ss()) [AC CONJ_ASSOC CONJ_COMM]
    (BETA_RULE for_storage_array_nil_core)) >>
  simp[] >> qexistsl [`bb`,`bod`,`cond`,`dv`,`eid`,`idx`,`len`,`lvo`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
  rewrite_tac[for_captured_storage_live_def] >> strip_tac >>
  `k = len` by
    (qpat_assum `[] = DROP k vs` (mp_tac o SYM) >>
     rewrite_tac[DROP_EQ_NIL] >> decide_tac) >>
  qpat_x_assum `k = len` SUBST_ALL_TAC >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
    mp_tac >> simp[NoAsms, AC CONJ_ASSOC CONJ_COMM]
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
  `SUC k <= len` by decide_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists `extra` >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl [`off`,`root`,`path`,`delta`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[IgnAsm `len = LENGTH vs`, IgnAsm `vs = GENLIST _ _`] >> rpt strip_tac
  >~ [`nb + w2n dst <= b \/ b + sz <= w2n dst`]
  >- (qpat_assum `!n b sz. local_region c0 ee.scopes s n b sz ==> _` drule >> decide_tac) >>
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

Definition for_captured_storage_round_scope_def:
  for_captured_storage_round_scope id tyv ei v =
    ei with scopes :=
      (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>)) :: ei.scopes
End

(* Recover the outer-scope resources at the actual scoped entry, not at the
   earlier scalar or expression endpoint. *)
Theorem for_captured_storage_outer_entry[local]:
  expr_sim_inv bc cx (extend_local env id typ F)
    (for_captured_storage_round_scope id tyv ei v) /\
  stmt_state_rel H ctx func bc cx (for_captured_storage_round_scope id tyv ei v) z /\
  cenv_top_ext c0 bc (for_captured_storage_round_scope id tyv ei v).scopes /\
  lookup_scopes id ei.scopes = NONE /\
  ret_pc_ok bc sb0 z /\ return_buf_frame d bc sb0 z /\
  (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  local_ptrs_reserved c0 sa0 /\ ~not_fresh_at sa0 p /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) ==>
  value_has_type tyv v /\ ret_pc_ok c0 sa0 z /\ return_buf_frame d c0 sa0 z /\
  w2n dst + nb <= z.vs_alloca_next /\
  (!name b sz. local_region c0 ei.scopes z name b sz ==>
   w2n dst + nb <= b \/ b + sz <= w2n dst)
Proof
  pure_rewrite_tac[for_captured_storage_round_scope_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `expr_sim_inv bc cx _ eb` >>
  `state_well_typed eb` by fs[expr_sim_inv_def] >>
  `value_has_type tyv v` by
    (drule lookup_scopes_state_well_typed_value_has_type >>
     disch_then (qspec_then `id` mp_tac) >>
     simp[Abbr `eb`,lookup_scopes_def,FLOOKUP_UPDATE]) >>
  `bc.ce_return_buf = c0.ce_return_buf /\ bc.ce_return_pc = c0.ce_return_pc` by
    (drule cenv_top_ext_same_frame >> simp[same_frame_def] >>
     disch_then (fn th => once_rewrite_tac[GSYM (CONJUNCT1 th)] >> simp[])) >>
  `ret_pc_ok c0 sa0 z` by fs[ret_pc_ok_def] >>
  `return_buf_frame d c0 sa0 z` by
    (Cases_on `d` >> gvs[return_buf_frame_def] >> PairCases_on `x` >>
     fs[return_buf_frame_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func c0 cx ei z` by
    (`ei = eb with scopes := ei.scopes` by simp[Abbr `eb`,evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >> irule stmt_state_rel_pop_top_ext >>
     reverse conj_tac >- (qexists `bc` >> simp[Abbr `eb`]) >>
     simp[Abbr `eb`,FDOM_FUPDATE]) >>
  qpat_assum `stmt_state_rel H ctx func c0 cx ei z`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `w2n dst + nb <= z.vs_alloca_next` by (drule_all alloca_site_registered_below >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `not_local_ptr c0 ei.scopes p` by metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

(* The scalar/copy endpoint supplies the resources for the scoped body. *)
Definition for_captured_storage_round_entry_def:
  for_captured_storage_round_entry exps (DF,lo,d,ctx,func) (cx,c0,bc,env,sb0,stmts)
    (e0,sa0,s0,G0,tn0) (idx,p,dst,lvo,len,inst,nb) (H,eb,j,z,GG,tt) <=>
    expr_sim_inv_mods c0.ce_modules bc cx env eb /\
    ce_locals_declared bc env /\ locals_alloc_ok bc env /\
    cenv_top_ext c0 bc eb.scopes /\ stmt_state_rel H ctx func bc cx eb z /\
    storage_well_formed_on cx eb (FST H) /\
    ghost_inv_at (DF H) lo d bc cx eb GG tt z /\
    ret_pc_ok bc sb0 z /\ return_buf_frame d bc sb0 z /\ return_buf_sep d bc eb z /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x z = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==> FLOOKUP GG x = FLOOKUP G0 x /\
                                op_taint tt (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 bc eb z /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa0.cs_next_id /\
      (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tt.t_mem ==> i IN tn0.t_mem) /\
    ~z.vs_halted /\ z.vs_current_bb = sb0.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    lookup_var idx z = SOME (n2w j) /\ FLOOKUP GG idx = NONE /\
    op_taint tt (Var idx) = {} /\ lookup_var p z = SOME dst /\
    eval_operand lvo z = SOME (n2w len) /\ op_prov GG lvo = NONE /\ op_taint tt lvo = {} /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dst,nb) /\ ptr_covers GG tt p z nb /\
    body_stmts_full_ok_mods c0.ce_modules exps cx stmts
End

(* Run one nonempty round. Cleanup and the backedge both use the actual
   scoped body endpoint, not the earlier scalar or expression endpoint. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  pure_rewrite_tac[for_array_loop_exit_def] >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result] >>
    gen_tac >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_state_updates] >>
    irule storage_trace_frame_finally >> simp[storage_trace_frame_pop_scope] >>
    irule storage_trace_frame_try >> simp[storage_trace_frame_loop_handler] >>
    irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_return,evaluate_storage_trace_frame]) >>
  conj_tac >- first_assum ACCEPT_TAC >> disch_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  ho_match_mp_tac (BETA_RULE (Q.INST [`ok` |-> `stmt_res_ok lctx`,
    `Guard` |-> `body_const_cells_agree [(NONE,cx_tops cx)] cx env`,
    `Entry` |-> `\H ei v j z GG tt.
      for_captured_storage_round_entry (DF,lo,d,ctx,func)
        (cx,c0,bc,extend_local env id typ F,sb0,stmts) (e0,sa0,s0,G0,tn0)
        (idx,p,dst,lvo,len,inst,nb)
        (H,for_captured_storage_round_scope id tyv ei v,j,z,GG,tt)`]
    (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV]))
      for_captured_storage_cons_from_stages))) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "head" >>
  conj_tac >- suspend "body" >> suspend "backedge"
QED
*)
Theorem for_captured_storage_round_from_head:
  body_inv (cx_tops cx) ctx bc cx /\ shadow_body_inv (cx_tops cx) ctx shadow_ctx /\
  supported_program (cx_tops cx) /\ get_module_code cx NONE = SOME (cx_tops cx) /\
  supported_stmts (cx_tops cx) bindings stmts /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) stmts ==>
      occurs_abi_decode_target target (cx_tops cx)) /\
  id NOTIN FDOM env.var_types /\ type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b /\
  stmts_exprs_ok bc stmts /\ call_evaluation_safe cx (int_calls_stmts stmts) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ bc ret_ty /\
  stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = (bc1,sb1) /\
  stmts_env (gas_shadow_env T bc) (InLoop exit incr) ret_ty (MAP gas_shadow_stmt stmts) shadow_sb0 = (gas_shadow_env T bc1,shadow_sb1) /\
  gas_shadow_state sb0 shadow_sb0 /\ gas_shadow_state sb1 shadow_sb1 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sb0 sb1 func /\ fn_has_code shadow_sb0 shadow_sb1 shadow_func /\
  (!H. dead_lo_ok H (DF H) lo bc cx) /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved bc sb0 /\ local_ptrs_reserved c0 sb0 /\ local_ptrs_reserved c0 sa0 /\
  (!x sz. bc.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb0 x) /\
  (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c0.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!x sz. c0.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  sa0.cs_next_id <= sb0.cs_next_id /\ sa0.cs_next_var <= sb0.cs_next_var /\
  sbExpr.cs_next_var <= sb0.cs_next_var /\
  ~block_is_terminated sb0 /\ not_fresh_at sb0 idx /\ not_fresh_at sb0 p /\
  (!x. lvo = Var x ==> not_fresh_at sb0 x) /\ (!lbl. lvo <> Label lbl) /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\ inst.inst_id = sd.cs_next_id /\
  ~not_fresh_at sa0 p /\ ~not_fresh_at sa0 idx /\ ~not_fresh_at sa0 out /\
  emit_jmp_if_not_terminated incr sb1 = ((),sj) /\ fn_has_code sb1 sj func /\
  si.cs_current_bb = incr /\ si.cs_current_insts = [] /\
  sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\ ~block_is_terminated sb /\
  emit_op ADD [Var idx; Lit 1w] si = (Var out,sk) /\
  emit_inst ASSIGN [Var out] [idx] sk = ((),sl) /\
  emit_inst JMP [Label cond] [] sl = ((),sm) /\ fn_has_code si sm func /\
  not_fresh_at si idx /\ p <> idx /\ p <> out /\
  (!x. lvo = Var x ==> x <> idx /\ x <> out) /\ (!x. bop = Var x ==> x <> idx /\ x <> out) /\
  ~s.vs_halted /\ (!f inst u. frag_reachable ctx func s f inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
      (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
      (lvo,idx,cond) (p,dst,nb,sd) (H,k,a::rs,es,G,tn,s)) /\
  body_const_cells_agree [(NONE,cx_tops cx)] cx env es /\
  gas_admissible (eval_for cx tyv id stmts (a::rs)) (stmt_res_ok lctx) es /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
      (bind (read_result cx a) (push_scope_with_var id tyv)) (es,s,G,tn)
      (\H res eb GG tt z. res = INL () /\ eb.gas_obs = [] /\
        ?v j. eb = for_captured_storage_round_scope id tyv (es with gas_obs := []) v /\
          read_result cx a es = (INL v,es) /\
          for_captured_storage_round_entry (DF,lo,d,ctx,func)
            (cx,c0,bc,extend_local env id typ F,sb0,stmts) (e0,sa0,s0,G0,tn0)
            (idx,p,dst,lvo,len,inst,nb) (H,eb,j,z,GG,tt) /\
          eval_operand bop z = SOME slot /\ op_taint tt bop = {} /\ a::rs = DROP j vs)
      (\H res ee gt r. ?ex. res = INR ex /\ for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
    (bind (read_result cx a) (\v. ignore_bind (push_scope_with_var id tyv v)
      (finally (try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception) pop_scope)))
    (es,s,G,tn)
    (\H res ee GG tt z. ee.gas_obs = [] /\ ~z.vs_halted /\
      ?b. res = INL b /\
        (b ==> for_array_loop_post (DF,lo,d,ctx,func) c0 cx lctx
          (e0,sa0,s0,G0,tn0) sb H (INL ()) ee GG tt z) /\
        (~b ==> body_const_cells_agree [(NONE,cx_tops cx)] cx env ee /\
          ?j. for_captured_storage_live (DF,lo,d,ctx,func,cx,c0,id,env,typ,stmts)
          (e0,sa0,s0,G0,tn0) (em,sbExpr,bop,tr,slot,tyv,bd,vs,len)
          (lvo,idx,cond) (p,dst,nb,sd) (H,j,rs,ee,GG,tt,z)))
    (\H res ee gt r. ?ex. res = INR ex /\ for_array_loop_exit ctx cx RetQ H (INR ex) ee gt r)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[head]:
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    simp[Abbr `H0`,GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> for_captured_storage_live _ _ _ _ _ _`
    (qspec_then `H0` (drule_then (strip_assume_tac o REWRITE_RULE [for_captured_storage_live_def]))) >>
  irule gas_outcome_full_post_mono >>
  qpat_assum `storage_trace_domain _ _ _ ==> gas_outcome_full _ _ _ _ _ _ _ _` drule >>
  disch_then (irule_at Any) >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> disch_then strip_assume_tac >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rename1 `a::rs = DROP j vs` >>
  rename1 `read_result cx a es = (INL v,es)` >>
  `j = k` by
    (qpat_assum `a::rs = DROP j vs` (mp_tac o AP_TERM ``LENGTH : eval_result list -> num``) >>
     qpat_assum `a::rs = DROP k vs` (mp_tac o AP_TERM ``LENGTH : eval_result list -> num``) >>
     simp[NoAsms,LENGTH_DROP] >> decide_tac) >>
  qpat_x_assum `j = k` SUBST_ALL_TAC >>
  qexists `v` >>
  qpat_assum `ee = for_captured_storage_round_scope _ _ _ _`
    (fn th => simp[NoAsms,GSYM th] >>
      conj_tac >- (pure_rewrite_tac[th,for_captured_storage_round_scope_def] >>
        simp[NoAsms,evaluation_state_fupdfupds])) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[body]:
  map_every qx_gen_tac [`v`,`eb`,`GG`,`tt`,`z`] >> strip_tac >>
  `for_captured_storage_round_scope id tyv (es with gas_obs := []) v = eb` by
    simp[for_captured_storage_round_scope_def,evaluation_state_fupdfupds] >>
  `eb.storage_trace = es.storage_trace` by simp[for_captured_storage_round_scope_def] >>
  qabbrev_tac `H0 = storage_trace_horizon eb.storage_trace` >>
  `valid_horizon cx st0 H0 eb.storage_trace` by simp[Abbr `H0`,GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H eb.storage_trace ==>
     for_captured_storage_round_entry _ _ _ _ _`
    (qspec_then `H0` (drule_then mp_tac)) >>
  qpat_assum `for_captured_storage_round_scope _ _ _ _ = eb`
    (fn th => simp[NoAsms,th,for_captured_storage_round_entry_def]) >>
  strip_tac >> suspend "invoke"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[backedge]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `si.cs_current_bb = incr` (SUBST_ALL_TAC o SYM) >>
  irule for_captured_storage_backedge >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`a`,`out`,`si`,`sk`,`sl`,`sm`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[invoke]:
  qabbrev_tac `ei = es with gas_obs := []` >>
  `body_const_cells_agree [(NONE,cx_tops cx)] cx env ei` by simp[Abbr `ei`] >>
  `eb = ei with scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv; value := v; popped := []|>))::ei.scopes` by
    (qpat_assum `for_captured_storage_round_scope _ _ _ _ = eb` mp_tac >>
     simp[for_captured_storage_round_scope_def,Abbr `ei`]) >>
  qpat_assum `eb = ei with scopes := _` (fn eq =>
    qpat_assum `expr_sim_inv bc cx _ eb` (assume_tac o PURE_REWRITE_RULE[eq])) >>
  RULE_ASSUM_TAC BETA_RULE >>
  `!H. valid_horizon cx st0 H eb.storage_trace ==>
     stmt_state_rel H ctx func bc cx eb z /\ storage_well_formed_on cx eb (FST H) /\
     ghost_inv_at (DF H) lo d bc cx eb GG tt z` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H eb.storage_trace ==>
       for_captured_storage_round_entry _ _ _ _ _`
       (qspec_then `H` (drule_then mp_tac)) >>
     qpat_assum `for_captured_storage_round_scope _ _ _ _ = eb`
       (fn eq => simp[NoAsms,eq,for_captured_storage_round_entry_def])) >>
  qpat_assum `frame_ret_ok_full _ _ _ _ _`
    (mp_then (Pat `frame_ret_ok_full _ _ _ _ _`) mp_tac (BETA_RULE for_storage_body_invoke_full)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `supported_stmts _ _ _`)) >>
  disch_then (drule_at (Pat `type_stmts _ _ _`)) >>
  disch_then (fn th => qpat_assum `stmts_env bc (InLoop exit incr) ret_ty stmts sb0 = _`
    (mp_then (Pat `stmts_env _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `stmts_env _ _ _ (MAP gas_shadow_stmt _) _ = _`
      (mp_then (Pat `stmts_env _ _ _ (MAP gas_shadow_stmt _) _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var idx z = _`
    (mp_then (Pat `lookup_var _ _ = SOME (n2w _)`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var p z = _`
    (mp_then (Pat `lookup_var _ _ = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  qpat_assum `eb = ei with scopes := _` (fn eq =>
    disch_then (mp_tac o PURE_REWRITE_RULE[GSYM eq])) >>
  disch_then (qspecl_then [`st0`,`GG`,`tt`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_stmts cx stmts)
    (eb,z,GG,tt) Qraw _` >>
  ho_match_mp_tac
    (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV]))
      for_body_cleanup_from_raw_landing) >>
  conj_tac >- (qpat_assum `eb = ei with scopes := _` SUBST1_TAC >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> suspend "raw_land"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[raw_land]:
  map_every qx_gen_tac [`H`,`raw`,`ef`,`G1`,`tn1`,`t`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  simp[NoAsms,Abbr `Qraw`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 strip_assume_tac
      (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  `valid_horizon cx st0 H eb.storage_trace` by
    (qpat_assum `?xs. !tail. eval_stmts _ _ _ = _`
       (qx_choose_then `xs` (qspec_then `[]`
         (mp_then (Pat `f st = (res,st')`) mp_tac valid_horizon_frame))) >>
     simp[evaluation_state_accfupds,CONJUNCT1 (CONJUNCT2 evaluate_storage_trace_frame)]) >>
  `body_const_cells_agree [(NONE,cx_tops cx)] cx env ef` by
    (`body_const_cells_agree [(NONE,cx_tops cx)] cx
         (extend_local env id typ F) (ef with gas_obs := [])` suffices_by simp[] >>
     irule body_const_cells_agree_stmts >>
     qpat_assum `?xs. !tail. eval_stmts _ _ _ = _`
       (qx_choose_then `xs` (qspec_then `[]` (irule_at (Pat `eval_stmts _ _ _ = _`)))) >>
     qexists_tac `ret_ty` >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `eb.storage_trace = es.storage_trace` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> for_captured_storage_live _ _ _ _ _ _`
    (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE [for_captured_storage_live_def]))) >>
  qpat_assum `!H. valid_horizon _ _ H eb.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  suspend "land_at"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[land_at]:
  `expr_sim_inv c0 cx env ei /\ lookup_scopes id ei.scopes = NONE /\
     cenv_top_ext c0 c0 ei.scopes` by simp[Abbr `ei`] >>
  `same_frame c0 bc` by
    (qpat_assum `cenv_top_ext c0 bc eb.scopes` (mp_then Any ACCEPT_TAC cenv_top_ext_same_frame)) >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at sb0 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. bop = Var x ==> not_fresh_at sb0 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `value_has_type tyv v /\ ret_pc_ok c0 sa0 z /\ return_buf_frame d c0 sa0 z /\
    w2n dst + nb <= z.vs_alloca_next /\
    (!name b sz. local_region c0 ei.scopes z name b sz ==>
       w2n dst + nb <= b \/ b + sz <= w2n dst)` by
    (MATCH_MP_TAC (REWRITE_RULE [for_captured_storage_round_scope_def]
       (INST_TYPE [alpha |-> ``:256``] for_captured_storage_outer_entry)) >>
     qpat_assum `eb = ei with scopes := _` (fn eq => pure_rewrite_tac[GSYM eq]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "apply_land"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[apply_land]:
  (* The local landing's entry register, provenance and taint state are
     the head endpoint, not the round's initial register state. *)
  mp_tac (Q.INST [`s` |-> `z`, `G` |-> `GG`, `tn` |-> `tt`,
                   `tops` |-> `cx_tops cx`]
    (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV]))
      (SPEC_ALL for_storage_body_post_land_at))) >>
  qpat_assum `eb = ei with scopes := _` (fn eq => pure_rewrite_tac[GSYM eq]) >>
  impl_tac >- suspend "land_inputs" >>
  suspend "pack_landing"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[land_inputs]:
  qpat_assum `inst.inst_id = sd.cs_next_id` (SUBST1_TAC o SYM) >>
  `w2n dst + nb < 2 ** 256` by
    (qpat_assum `w2n dst + nb < dimword (:256)` mp_tac >> simp[NoAsms,dimword_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[pack_landing]:
  strip_tac >> qexistsl [`sc`,`rest`,`b`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (disch_tac >> qpat_assum `b ==> ?c. stmt_lands _ _ _ _ /\ P c`
       (drule_then (qx_choose_then `c` strip_assume_tac)) >>
      qpat_x_assum `c = c0` SUBST_ALL_TAC >>
      simp_tac bool_ss [for_array_loop_post_def] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  disch_tac >>
  qpat_x_assum `~b ==> _` (drule_then strip_assume_tac) >>
  suspend "pack_live"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_captured_storage_round_from_head[pack_live]:
  conj_tac >- simp[] >>
  conj_tac >- (
    `ei.storage_trace = es.storage_trace` by simp[Abbr `ei`] >>
    `(ef with scopes := rest).storage_trace =
       em.storage_trace ++ (extra ++ delta')` by
      simp[APPEND_ASSOC] >>
    `(if raw = INL () then jump_to incr t else t).vs_current_bb = incr /\
     (if raw = INL () then jump_to incr t else t).vs_inst_idx = 0` by simp[] >>
    pure_rewrite_tac[for_captured_storage_live_def] >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- (qexists `extra ++ delta'` >> first_assum ACCEPT_TAC) >>
    conj_tac >- (qexistsl [`off`,`root`,`path`,`delta`] >>
                 rpt conj_tac >> first_assum ACCEPT_TAC) >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise for_captured_storage_round_from_head
*)
