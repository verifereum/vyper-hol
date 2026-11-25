(* The constructor word snapshot includes exactly the scalar unwrap cut. *)
Theory entryCreateCtorWordScope
Ancestors
  entryCreateFocusSpec createCtorSavedSimple bodyFullCreateHeld
  fragGasOriginPtrExec gasShadowCompileBase exprSimSource stmtSimDefs
  exprLowering exprLoweringProps exprSimFullBundleProps exprSimWordArgs loweringPosts
  bodyMemoryDefs vyperState bodyPtrDefs exprSimMemDefs exprSimHyps
  aggregateEvaluatedLayout abiEncodeArgsSim context compileEnv s1PrefixDefs
  entryCreateCompletedCut exprReasonOperand exprBodyPreProps

Theorem ctor_word_scalar_post[local]:
  is_word_type (expr_type e) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,ss) /\
  return_buf_frame d ce sa s0 /\ ~t.vs_halted /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (res,ee) /\
  expr_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,ss,s0,op,G0,tn0) H res ee G tn t ==>
  ?v. res = INL v /\
    (?raw. read_result cx raw ee = (INL v,ee) /\
      vv_holds ce cx (expr_type e) raw (StackValue (expr_type e) op) ee t /\
      vv_at ce cx (expr_type e) sa ss ee raw (StackValue (expr_type e) op) t /\
      ptr_vv_ok cx (expr_type e) raw (StackValue (expr_type e) op) ee G tn t /\
      vv_store_bound cx (expr_type e) (expr_type e) ee raw (StackValue (expr_type e) op) t) /\
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d ce ss t /\ ghost_inv_at (DF H) lo d ce cx ee G tn t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = ss.cs_current_bb /\ t.vs_inst_idx = LENGTH ss.cs_current_insts /\
    wb_frame ce es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  strip_tac >>
  drule eval_read_preserves_scopes_dom >> simp[] >> strip_tac >>
  `sa.cs_next_var <= ss.cs_next_var` by
    (qspec_then `sa` mp_tac (Q.SPECL [`ce`,`expr_type e`,`e`]
       ci_mono_lower_value_compile_expr) >> simp[ci_mono_def]) >>
  gvs[expr_sim_full_post_def, expr_sim_full_endpoint_def] >>
  drule expr_post_frame >> strip_tac >> fs[expr_post_def] >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_word] >>
  fs[] >>
  `return_buf_frame d ce ss t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> simp[]) >>
  conj_tac >- (qexists_tac `Value v` >>
    simp[read_result_def,return_def,vv_holds_def,vv_at_def,ptr_vv_ok_def,
         vv_store_bound_def]) >>
  simp[read_result_def,return_def,vv_holds_def,vv_at_def,ptr_vv_ok_def,
       vv_store_bound_def]
QED

Theorem create_ctor_word_head_scoped:
  expr_body_pre ce cx env e es /\ is_word_type (expr_type e) /\
  expr_sim_scoped (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sh = (vv,shm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) shm = (sv,shs) /\
  gas_shadow_state sa sh /\ gas_shadow_state ss shs /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa ss func /\
  fn_has_code sh shs shadow_func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa ss (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      ((?tag op. sv = StackValue tag op) \/
       (?p. sv = LocatedValue (lowered_value_type ce e) p /\
         ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type ce e) p /\
         ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
         lowered_value_type ce e = expr_type e /\ sv = vv)) /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds ce cx (lowered_value_type ce e) raw sv ee t /\
        vv_at ce cx (lowered_value_type ce e) sa ss ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type ce e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      ((case sv of StackValue _ _ => ~is_word_type (lowered_value_type ce e)
                  | LocatedValue _ p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok ce e (vv_operand sv) G t) /\
      (copy /\ ~is_word_type (lowered_value_type ce e) ==>
        ?x w tv. vv_location sv = SOME LocMemory /\ vv_operand sv = Var x /\
          eval_operand (vv_operand sv) t = SOME w /\
          evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ val_wf tv v /\
          FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          sm.cs_next_id < ss.cs_next_id /\
          (!n b len. local_region ce ee.scopes t n b len ==>
             regions_disjoint (w2n w) (type_memory_size tv) b len)) /\
      stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d ce ss t /\ ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
      t.vs_current_bb = ss.cs_current_bb /\ t.vs_inst_idx = LENGTH ss.cs_current_insts /\
      wb_frame ce es ee sa s0 t /\ MAP FDOM ee.scopes = MAP FDOM es.scopes)
    (create_operand_exit_post ctx cx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `is_word_type (lowered_value_type ce e) /\ lowered_value_type ce e = expr_type e` by
    metis_tac[arg_type_fits_word_type,abi_args_word_fits_eq] >>
  drule_all ctor_snapshot_word_lower_value >> strip_tac >>
  `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
     (gas_shadow_expr e) sh = (op,shs)` by
    (`reason_uniform_shape compile_expr ce (expr_type e) e` by
       (irule compile_expr_reason_uniform >> qexists_tac `env` >>
        drule expr_body_pre_static_facts >> simp[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     `vv_type vv = expr_type e` by
       (fs[reason_uniform_shape_def] >>
        qpat_x_assum `!s. _` drule >>
        Cases_on `vv` >> gvs[reason_result_shape_def,vv_type_def]) >>
     `ext_call_arg_value (lowered_value_type ce e) vv = vv` by
       (Cases_on `vv` >> gvs[ext_call_arg_value_def,vv_type_def]) >>
     Cases_on `unwrap_value ce vv shm` >>
     fs[lower_value_def,compile_snapshot_vv_def,comp_bind_def,comp_return_def]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es (st0,sa,ss,sh,shs,op,s0,G0,tn0)` by
    (drule_then assume_tac expr_body_pre_gas_admissible >>
     simp[expr_sim_full_pre_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_scoped _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_scoped_def]) >>
  disch_then (drule_then mp_tac) >>
  rw[scoped_operand_outcome_def] >>
  qexists_tac `marks`
  >- (disj1_tac >> simp[] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      map_every qexists_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ _ _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        drule >> strip_tac
      >- (`~t.vs_halted` by
            (drule gas_origin_ptr_path_exec >> simp[fragExecTheory.exit_result_def]) >>
          qpat_assum `!tail. _` (qspec_then `[]` assume_tac) >>
          disj1_tac >> qexists_tac `t` >> simp[] >>
          drule_all ctor_word_scalar_post >> simp[]) >>
      simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED
