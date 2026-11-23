(* A mapping reference is a separate result mode: there is no value read
   between the compiled base and its selected key expression. *)
Theory entryCreateSubscriptMapSpec
Ancestors
  entryCreateFocusSpec entryCreateCompletedCut exprSimFullBundleProps
  bodySimFull exprSimMapDefs exprSimDefs gasContext gasOutcomeFull
  gasExplicitSites gasShadow gasShadowCompileBase
  bodyPtrDefs loweringPosts loweringStateRelDefs ptrDiscipline allocaHistory
  vyperStorageFootprint vyperStoragePlaceProvenance vyperInterpreter vyperState
  exprLowering context compileEnv fragExec venomState finite_map list pair

Definition expr_map_sim_full_pre_def:
  expr_map_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) <=>
    compile_expr ce ty e sa = (vv,sb) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (vv,shb) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (sa,sb,sha,shb) /\
    local_ptrs_reserved ce sa /\
    (!H. dead_lo_ok H (DF H) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_expr cx e) expr_map_res_ok es /\
    return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func ce cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ create_operand_at sa s0
End

Definition expr_map_sim_full_post_def:
  expr_map_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,vv,G0,tn0) =
    \H res ee G tn t. ?tr slot kt vt tp p.
      res = INL (HashMapRef tr slot kt vt) /\
      storage_mapping_region cx tr slot (HashMapT kt vt) /\
      vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
      eval_operand p.ptr_operand t = SOME slot /\
      stmt_state_rel H ctx func ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) ==>
         mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
      locals_kept ce es ee s0 t /\
      (~expr_has_effect e ==> pure_frame ce func es sa s0 t) /\
      return_buf_frame d ce sa t /\ expr_sim_full_endpoint func sb s0 t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
End

Theorem map_exit_post_eq[local]:
  create_operand_exit_post ctx cx =
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  simp[FUN_EQ_THM, create_operand_exit_post_def]
QED

(* Check that the bundled pre and posts are those of the existing judgment. *)
Theorem expr_map_sim_full_via_bundle:
  expr_map_sim_full (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es <=>
  !st0 sa sb sha shb vv s0 G0 tn0.
    expr_map_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
      (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_expr cx e) (es,s0,G0,tn0)
      (expr_map_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0))
      (create_operand_exit_post ctx cx)
Proof
  simp[expr_map_sim_full_def, expr_map_sim_full_pre_def, expr_sim_full_code_def,
       expr_map_sim_full_post_def, expr_sim_full_endpoint_def, create_operand_at_def,
       map_exit_post_eq, AC CONJ_ASSOC CONJ_COMM]
QED

Definition expr_map_sim_scoped_at_def:
  expr_map_sim_scoped_at L (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) <=>
    (expr_map_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
       (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ L sa sb ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (cx_tops cx) cx st0 sa sb (eval_expr cx e) (es,s0,G0,tn0)
       (expr_map_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0))
       (create_operand_exit_post ctx cx) /\
     create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func
       (cx_tops cx) cx st0 (eval_expr cx e) (es,s0))
End

Theorem expr_map_sim_scoped_at_full:
  expr_map_sim_scoped_at L (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  expr_map_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\ L sa sb ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_expr cx e) (es,s0,G0,tn0)
    (expr_map_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  rw[expr_map_sim_scoped_at_def] >>
  irule scoped_operand_outcome_full >> metis_tac[]
QED
