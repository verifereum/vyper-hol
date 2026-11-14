(* Concrete continuation after the two full value-producing child executions.
   The source equations and complete child posts share fixed endpoints; no
   horizon is allowed to choose a different runtime execution or ghost. *)
Theory bodyFullBuiltinECArithContinuation
Ancestors
  bodyFullBuiltinECArithOperands bodyFullBuiltinPrecompileSuffixSuccess
  bodyFullBuiltinPrecompileSuffixAbort bodyFullAllocaFresh bodyFullAllocGeneric
  bodyFullUnwrapRun bodyFullGhostFrame bodyMemEcArithTransfers bodyMemEcArithSafe
  bodyMemEcArithCode
  bodySimFull bodyFullPreds exprSimECArith gasOutcomeFullCompose
  gasShadowCompile exprSimHypsDefs exprLowering loweringPosts vyperAST list
  vyperStorageTrace vyperStorageFootprint exprSimHyps exprSimOperands exprSimSource

Theorem ec_arith_tail_full:
  (bt = ECAdd \/ bt = ECMul) /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
  body_exprs_full_ok cx [e1;e2] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin a bt [e1;e2]) es /\
  compile_expr cenv ty (Builtin a bt [e1;e2]) sa = (vv,sb) /\
  compile_expr cenv ty (gas_shadow_expr (Builtin a bt [e1;e2])) shadow_sa =
    (vv,shadow_sb) /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr cenv (expr_type e2) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  (if bt = ECAdd then compile_ecadd_points x y s2
   else compile_ecmul_point x y s2) = (res,sb) /\
  vv = FST (as_ptr_val a LocMemory (res,sb)) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state s1 shadow_s1 /\
  gas_shadow_state s2 shadow_s2 /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  gas_admissible (eval_expr cx (Builtin a bt [e1;e2])) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ tail) =
      (INL v1,es1 with gas_obs := tail)) /\
  storage_trace_domain cx st0 es1.storage_trace /\
  ~t1.vs_halted /\ es1.gas_obs = [] /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
    expr_store_bound cx (expr_type e1) v1 x t1 /\
    t1.vs_current_bb = s1.cs_current_bb /\
    t1.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t1 /\ s0.vs_alloca_next <= t1.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx es1 G1 tn1 t1 /\
    ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t1 /\
    (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t1) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
      (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ tail) =
      (INL v2,es2 with gas_obs := tail)) /\
  storage_trace_domain cx st0 es2.storage_trace /\
  ~t2.vs_halted /\ es2.gas_obs = [] /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    expr_store_bound cx (expr_type e2) v2 y t2 /\
    t2.vs_current_bb = s2.cs_current_bb /\
    t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func t2 /\ t1.vs_alloca_next <= t2.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx es2 G2 tn2 t2 /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 t2 /\
    (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 y G2 t2) /\
    ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2])
    (es2,t2,G2,tn2)
    (\H rr ee G tn t. ?tv. rr = INL tv /\
      vv_post H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee tv vv t /\
      vv_store_bound cx (expr_type (Builtin a bt [e1;e2]))
        (lowered_value_type cenv (Builtin a bt [e1;e2])) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Builtin a bt [e1;e2])) tv vv ee G tn t /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Builtin a bt [e1;e2])) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      (!ty' op. vv = StackValue ty' op /\
        ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) op G t) /\
      (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H rr ee gt r. expr_exit rr r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ es1.gas_obs) =
     (INL v1,es1)` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `es1.gas_obs` mp_tac) >> simp[]) >>
  `bind (eval_expr cx e2) (read_result cx)
     (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ es2.gas_obs) =
     (INL v2,es2)` by
    (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `es2.gas_obs` mp_tac) >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx e1) (read_result cx)) /\
   storage_trace_frame (bind (eval_expr cx e2) (read_result cx))` by
    (conj_tac >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result, evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
       valid_horizon cx st0 H es1.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `bind (eval_expr cx e2) _ _ = _`
       (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
     simp[] >> strip_tac >> gvs[valid_horizon_def]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!n. bt <> Slice n` by (rpt strip_tac >> gvs[]) >>
  `expr_body_pre cenv cx env e1 es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e1`,`es`] mp_tac) >> simp[]) >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_ec_point >> simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >> fs[expr_body_pre_def]) >>
  qpat_assum `lower_value _ _ _ e1 _ = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ e2 _ = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `bind (eval_expr cx e2) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
           exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es1.storage_trace` by
    metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _`
    (qspec_then `storage_trace_horizon es2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon es2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `safe_operand s1 x` by
    (irule ec_point_lower_value_safe_operand >> metis_tac[]) >>
  `(!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    fs[exprSafeOperandTheory.safe_operand_def] >>
  drule_all expr_post_operand_word >> strip_tac >>
  `!w. eval_operand x t1 = SOME w ==> eval_operand x t2 = SOME w` by
    metis_tac[optionTheory.SOME_11] >>
  drule_all ec_first_point_staging_ready >> strip_tac >>
  `cs_extends s2 sb` by
    (Cases_on `bt = ECAdd` >> gvs[] >>
     metis_tac[externalEntryShapeTheory.compile_ecadd_points_labels,
               externalEntryShapeTheory.compile_ecmul_point_labels, pairTheory.SND]) >>
  `cs_extends s1 sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code s2 sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!i. MEM i (emitted_insts s2 sb) ==> MEM i (fn_insts func)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  Cases_on `bt = ECAdd`
  >- (gvs[] >> drule_all ecadd_points_prefix >> strip_tac >>
      FAIL_TAC "ECAdd full allocation path") >>
  gvs[] >> drule_all ecmul_points_prefix >> strip_tac >>
  FAIL_TAC "ECMul full allocation path"
QED
