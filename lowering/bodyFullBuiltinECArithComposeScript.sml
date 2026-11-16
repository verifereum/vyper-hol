(* Sequential full child composition, conditional on the concrete EC tail. *)
Theory bodyFullBuiltinECArithCompose
Ancestors
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimECArith bodyInvNoDalloca
  gasOutcomeFullCompose gasShadowCompile gasShadowCompileStmtHelpers
  exprSimHypsDefs exprLowering
  loweringPosts vyperAST list vyperStorageTrace exprSimHyps exprSimSource

Theorem ec_arith_vv_from_tail_full:
  (!bt a e1 e2 cx tops ctx cenv env es ty sa vv sb shadow_sa shadow_sb
    x s1 y s2 shadow_s1 shadow_s2 res shadow_ctx func shadow_func DF lo
    d PG s0 st0 G0 tn0 marks1 v1 es1 t1 G1 tn1 marks2 v2 es2 t2 G2 tn2.
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
      expr_store_bound cx (post_value_type cenv e1) v1 x t1 /\
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
      expr_store_bound cx (post_value_type cenv e2) v2 y t2 /\
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
      (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r)) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  disch_then (mk_asm "tail") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~ctx_has_dalloca ctx` by (drule body_inv_no_dalloca >> simp[]) >>
  `a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
   ?e1 e2. args = [e1;e2] /\
     expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     expr_type e2 = (if bt = ECAdd then
       ArrayT (BaseT (UintT 256)) (Fixed 2) else BaseT (UintT 256))` by
    (asm_x "tail" kall_tac >>
     Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[ec_pre_types]) >>
  `body_exprs_full_ok cx [e1;e2]` by
    (gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?x y s1 s2 res.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
    (if bt = ECAdd then compile_ecadd_points x y s2
     else compile_ecmul_point x y s2) = (res,sb) /\
    vv = FST (as_ptr_val a LocMemory (res,sb))` by
    (asm_x "tail" kall_tac >>
     Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[compile_ec_operands]) >>
  `?shadow_s1. lower_value compile_expr cenv (expr_type e1)
      (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
      gas_shadow_state s1 shadow_s1` by
    (asm_x "tail" kall_tac >>
     mp_tac (Q.INST [`ty` |-> `expr_type e1`, `e` |-> `e1`]
       gas_shadow_stmt_lower_value) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv (expr_type e1)
       (gas_shadow_expr e1) shadow_sa` >> gvs[]) >>
  `?shadow_s2. lower_value compile_expr cenv (expr_type e2)
      (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
      gas_shadow_state s2 shadow_s2` by
    (asm_x "tail" kall_tac >>
     mp_tac (Q.INST [`ty` |-> `expr_type e2`, `e` |-> `e2`]
       gas_shadow_stmt_lower_value) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`,`shadow_s1`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv (expr_type e2)
       (gas_shadow_expr e2) shadow_s1` >> gvs[]) >>
  `expr_body_pre cenv cx env e1 es` by
    (asm_x "tail" kall_tac >>
     irule exprOpenFirstOperandTheory.expr_body_pre_builtin_head >>
     goal_assum (drule_at Any) >> rpt strip_tac >> gvs[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e1) e1 es` by
    (asm_x "tail" kall_tac >>
     qpat_assum `body_exprs_full_ok _ _` mp_tac >>
     pure_rewrite_tac[body_exprs_full_ok_def] >> strip_tac >>
     qpat_assum `body_expr_full_ok _ e1`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  qpat_assum `lower_value _ _ _ e1 sa = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ e2 s1 = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  `cs_extends s2 sb` by
    (asm_x "tail" kall_tac >>
     Cases_on `bt = ECAdd` >> gvs[] >>
     metis_tac[externalEntryShapeTheory.compile_ecadd_points_labels,
               externalEntryShapeTheory.compile_ecmul_point_labels, pairTheory.SND]) >>
  `cs_extends s1 sb` by
    (asm_x "tail" kall_tac >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 sb func` by
    (asm_x "tail" kall_tac >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `?shadow_res. (if bt = ECAdd then compile_ecadd_points x y shadow_s2
       else compile_ecmul_point x y shadow_s2) = (shadow_res,shadow_sb)` by
    (asm_x "tail" kall_tac >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (assume_tac o REWRITE_RULE [gasShadowTheory.gas_shadow_expr_def,listTheory.MAP]) >>
     Cases_on `bt = ECAdd`
     >- (gvs[gasShadowTheory.gas_shadow_builtin_def] >>
         qpat_assum `compile_expr _ _ (Builtin _ ECAdd _) shadow_sa = _`
           (mp_then Any mp_tac (CONJUNCT2 compile_ec_operands)) >>
         simp[gasShadowTheory.gas_shadow_expr_type] >> metis_tac[]) >>
     gvs[gasShadowTheory.gas_shadow_builtin_def] >>
     qpat_assum `compile_expr _ _ (Builtin _ ECMul _) shadow_sa = _`
       (mp_then Any mp_tac (CONJUNCT1 compile_ec_operands)) >>
     simp[gasShadowTheory.gas_shadow_expr_type] >> metis_tac[]) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  `cs_extends shadow_s2 shadow_sb` by
    (asm_x "tail" kall_tac >> Cases_on `bt = ECAdd` >> gvs[] >>
     metis_tac[externalEntryShapeTheory.compile_ecadd_points_labels,
               externalEntryShapeTheory.compile_ecmul_point_labels, pairTheory.SND]) >>
  `cs_extends shadow_s1 shadow_sb` by
    (asm_x "tail" kall_tac >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code shadow_sa shadow_s1 shadow_func /\
   fn_has_code shadow_s1 shadow_s2 shadow_func` by
    (asm_x "tail" kall_tac >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e1 _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,
     `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (asm_x "tail" kall_tac >>
    metis_tac[expr_body_pre_gas_admissible])) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `eval_expr cx (Builtin a bt [e1;e2]) =
    bind (bind (eval_expr cx e1) (read_result cx))
      (\v1. bind (bind (eval_expr cx e2) (read_result cx))
        (\v2. ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2]))` by
    (irule ec_eval_bind >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> asm_x "tail" kall_tac >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >> reverse conj_tac
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      gen_tac >> BETA_TAC >> asm_x "tail" kall_tac >>
      rewrite_tac[storage_trace_frame_def] >> rpt gen_tac >>
      drule ec_source_tail_cases >> disch_then (fn th => rewrite_tac[th]) >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt CASE_TAC >>
      gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\
                 ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "first_success" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `res'` >- simp[] >>
  simp[exprSimDefsTheory.halt_exit_def] >>
  Cases_on `r` >> Cases_on `y` >>
  simp[exprSimDefsTheory.expr_exit_def] >>
  Cases_on `e` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume ec_arith_vv_from_tail_full[first_success]:
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?v1. res' = INL v1` by
    (asm_x "tail" kall_tac >> fs[Abbr `childQ`] >> metis_tac[]) >>
  qpat_x_assum `res' = INL _` SUBST_ALL_TAC >>
  simp_tac (srw_ss()) [] >>
  `~t.vs_halted /\ mid.gas_obs = []` by
    (asm_x "tail" kall_tac >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     childQ H (INL v1) mid G1 tn1 t` by
    (asm_x "tail" kall_tac >> metis_tac[]) >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v1,mid)` by
    (qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `expr_sim_inv cenv cx env mid` by
    (asm_x "tail" kall_tac >>
     `expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     qpat_x_assum `expr_body_pre _ _ _ _ (_ with gas_obs := _)`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_eval) >>
     simp[ETA_THM] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (asm_x "tail" kall_tac >>
     irule exprSimSourceTheory.expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     qexistsl_tac [`a`,`[e1;e2]`,`bt`,`es`] >>
     simp[] >> Cases_on `bt = ECAdd` >> gvs[]) >>
  `body_expr_full_ok cx e2` by
    (asm_x "tail" kall_tac >>
     qpat_x_assum `body_exprs_full_ok _ _` mp_tac >>
     rewrite_tac[body_exprs_full_ok_def] >>
     strip_tac >> first_x_assum irule >>
     qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid` by
    (asm_x "tail" kall_tac >>
     qpat_x_assum `body_expr_full_ok _ e2`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
    expr_store_bound cx (post_value_type cenv e1) v1 x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
    (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (asm_x "tail" kall_tac >> fs[Abbr `childQ`] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`s1`,`s2`,`shadow_s1`,`shadow_s2`,`y`,
     `t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (asm_x "tail" kall_tac >>
    `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
       e1 es sa s1 s0 mid v1 x t /\ alloca_history func t /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts` by metis_tac[] >>
    `return_buf_frame d cenv s1 t` by
      (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
       goal_assum (drule_at Any) >>
       fs[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
    `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
      (rpt strip_tac >>
       qpat_x_assum `!H. _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
         drule >> simp[loweringPostsTheory.expr_post_def]) >>
    simp[] >> rpt conj_tac
    >~ [`local_ptrs_reserved cenv s1`]
    >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]
    >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[])
    >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[])
    >~ [`gas_admissible _ _ _`]
    >- metis_tac[expr_body_pre_gas_admissible] >>
    rpt strip_tac >> drule contextRawReachableTheory.frag_reachable_members >>
    simp[] >> strip_tac >>
    fs[ptrDisciplineTheory.ctx_has_dalloca_def,EXISTS_MEM] >>
    simp[unitMemInvTheory.dalloca_no_wrap_def] >> metis_tac[])) >> strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ (mid,_,_,_) _ _`
    (fn th => qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) childQ2 childR2`) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`,`t'`,`v`] >> asm_x "tail" kall_tac >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >- (gen_tac >> BETA_TAC >> asm_x "tail" kall_tac >>
      rewrite_tac[storage_trace_frame_def] >> rpt gen_tac >>
      drule ec_source_tail_cases >> disch_then (fn th => rewrite_tac[th]) >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt CASE_TAC >>
      gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  qexists_tac `\H res ee G tn t. childQ2 H res ee G tn t /\
                 ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "second_success" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ (mid,_,_,_) _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR2`] >> rpt strip_tac >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `res'` >- simp[] >>
  simp[exprSimDefsTheory.halt_exit_def] >>
  Cases_on `r` >> Cases_on `y` >>
  simp[exprSimDefsTheory.expr_exit_def] >>
  Cases_on `e` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume ec_arith_vv_from_tail_full[second_success]:
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace)
      mid'.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?v2. res' = INL v2` by
    (asm_x "tail" kall_tac >> fs[Abbr `childQ2`] >> metis_tac[]) >>
  qpat_x_assum `res' = INL _` SUBST_ALL_TAC >>
  simp_tac (srw_ss()) [] >>
  `~t'.vs_halted /\ mid'.gas_obs = []` by
    (asm_x "tail" kall_tac >> metis_tac[]) >>
  qpat_assum `~ctx_has_dalloca ctx`
    (fn th => rewrite_tac [th,loweringPostsTheory.post_value_type_def]) >>
  asm "tail" (irule o PURE_REWRITE_RULE [loweringPostsTheory.post_value_type_def]) >>
  asm_x "tail" kall_tac >>
  qpat_assum `compile_expr cenv ty (Builtin _ _ _) sa = _` (irule_at Any) >>
  qpat_assum `compile_expr _ _ _ shadow_sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ e1 sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ e2 s1 = _` (irule_at Any) >>
  simp[Abbr `childQ2`] >>
  qexistsl_tac [`tops`, `tn1`, `t`, `shadow_s2`, `shadow_func`,
                `marks'`, `marks`, `mid`, `env`, `G1`] >>
  gvs[] >> metis_tac[]
QED

Finalise ec_arith_vv_from_tail_full
