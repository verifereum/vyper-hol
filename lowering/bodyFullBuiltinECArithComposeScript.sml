(* The two argument reads share their actual compiler and execution cuts.
   Only the continuation at two successful reads needs the EC arithmetic tail. *)
Theory bodyFullBuiltinECArithCompose
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull exprSimECArith
  bodyFullIfExpReach[qualified,ignore_grammar]
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  gasOutcomeFullCompose gasShadowCompile gasShadowCompileStmtHelpers
  exprSimHypsDefs exprLowering loweringPosts vyperAST list
  vyperStorageTrace exprSimHyps exprSimSource
  bodyFullBuiltinECArithStaging bodyFullBuiltinECArithPermitted
  bodyFullBuiltinECArithEmpty bodyFullOfVV exprSimWordArgs
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

Theorem ec_arith_vv_from_tail_full:
  (!bt a e1 e2 cx tops ctx cenv env es ty sa vv sb shadow_sa shadow_sb
    x s1 y s2 shadow_s1 shadow_s2 res shadow_ctx func shadow_func DF lo
    d PG s0 st0 G0 tn0 marks1 v1 es1 t1 G1 tn1 marks2 v2 es2 t2 G2 tn2.
    (bt = ECAdd \/ bt = ECMul) /\
    a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
    body_exprs_full_ok_mods mods exps cx [e1;e2] /\ (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt [e1;e2]) es /\
    compile_expr cenv ty (Builtin a bt [e1;e2]) sa = (vv,sb) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin a bt [e1;e2])) shadow_sa =
      (vv,shadow_sb) /\
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa =
      (x,shadow_s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2) (gas_shadow_expr e2) shadow_s1 =
      (y,shadow_s2) /\
    (if bt = ECAdd then compile_ecadd_points x y s2
     else compile_ecmul_point x y s2) = (res,sb) /\
    vv = FST (as_stack_val a (res,sb)) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state s1 shadow_s1 /\
    gas_shadow_state s2 shadow_s2 /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
        vv_store_bound cx (post_value_type cenv (Builtin a bt [e1;e2]))
          (lowered_value_type cenv (Builtin a bt [e1;e2])) ee tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_vv_ok cx (post_value_type cenv (Builtin a bt [e1;e2])) tv vv ee G tn t /\
        (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) /\
          ~is_bytestring_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
          vv_own cenv cx (post_value_type cenv (Builtin a bt [e1;e2])) sa sb ee tv vv t /\
          (!ty' p. vv = LocatedValue ty' p ==> p.ptr_location = LocMemory)) /\
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
      (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  disch_then (mk_asm "tail") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
   ?e1 e2. args = [e1;e2] /\
     expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     expr_type e2 = (if bt = ECAdd then
       ArrayT (BaseT (UintT 256)) (Fixed 2) else BaseT (UintT 256))` by
    (asm_x "tail" kall_tac >>
     Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[ec_pre_types]) >>
  `body_exprs_full_ok cx [e1;e2]` by
    gvs[vyperContextTheory.builtin_args_length_ok_def] >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?x y s1 s2 res.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
    (if bt = ECAdd then compile_ecadd_points x y s2
     else compile_ecmul_point x y s2) = (res,sb) /\
    vv = FST (as_stack_val a (res,sb))` by
    (asm_x "tail" kall_tac >>
     Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[compile_ec_operands]) >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e1) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = (shadow_x,shadow_s1)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e1 sa = (x,s1)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `shadow_x = x` SUBST_ALL_TAC >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
      (gas_shadow_expr e2) shadow_s1` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = (shadow_y,shadow_s2)` >>
  `shadow_y = y /\ gas_shadow_state s2 shadow_s2` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e2 s1 = (y,s2)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `shadow_y = y` SUBST_ALL_TAC >>
  `expr_body_pre cenv cx env e1 es` by
    (irule exprOpenFirstOperandTheory.expr_body_pre_builtin_head >>
     goal_assum (drule_at Any) >> rpt strip_tac >> gvs[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e1) e1 es` by
    (qpat_assum `body_exprs_full_ok _ _` mp_tac >>
     pure_rewrite_tac[body_exprs_full_ok_def] >> strip_tac >>
     qpat_assum `body_expr_full_ok _ e1`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     qpat_assum `!df l dd pg ts c sc f sf ce en ty' ee.
                  _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
       mp_tac >>
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
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
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
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `shadow_s2` >> simp[]) >>
  `fn_has_code shadow_sa shadow_s1 shadow_func /\
   fn_has_code shadow_s1 shadow_sb shadow_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_s1 shadow_s2 shadow_func /\
   fn_has_code shadow_s2 shadow_sb shadow_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e1 _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,
     `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (asm_x "tail" kall_tac >>
    simp[] >> metis_tac[expr_body_pre_gas_admissible])) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `eval_expr cx (Builtin a bt [e1;e2]) =
    bind (bind (eval_expr cx e1) (read_result cx))
      (\v1. bind (bind (eval_expr cx e2) (read_result cx))
        (\v2. ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2]))` by
    (irule ec_eval_bind >> simp[]) >>
  pop_assum SUBST1_TAC >> BETA_TAC >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[ec_source_tail_storage_frame] >> irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
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
  simp[exprSimHashTheory.expr_exit_INR_cast, exprSimDefsTheory.halt_exit_def]
QED

Resume ec_arith_vv_from_tail_full[first_success]:
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?v1. res' = INL v1` by
    (asm_x "tail" kall_tac >> fs[Abbr `childQ`] >> metis_tac[]) >>
  qpat_x_assum `res' = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v1` >> (conj_tac >- REFL_TAC) >> BETA_TAC >>
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
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by
       qpat_assum `expr_body_pre _ cx env e1 _`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_assum `bind (eval_expr cx e1) (read_result cx) _ = _`
       (mp_then (Pos last) (qspec_then `cenv` mp_tac)
         (REWRITE_RULE [ETA_THM] exprSimSourceTheory.expr_body_pre_eval)) >>
     disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     qexistsl_tac [`a`,`[e1;e2]`,`bt`,`es`] >>
     simp[] >> Cases_on `bt = ECAdd` >> gvs[]) >>
  `body_expr_full_ok cx e2` by
    (qpat_x_assum `body_exprs_full_ok _ _` mp_tac >>
     rewrite_tac[body_exprs_full_ok_def] >>
     strip_tac >> first_x_assum irule >>
     qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid` by
    (qpat_x_assum `body_expr_full_ok _ e2`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     qpat_assum `!df l dd pg ts c sc f sf ce en ty' ee.
                  _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
       mp_tac >>
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
    `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
      (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
          stmt_state_rel H ctx func cenv cx mid t /\ _`
         (qspec_then `storage_trace_horizon mid.storage_trace`
           (drule_then (ACCEPT_TAC o
              MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
              CONJUNCT1)))) >>
    simp[] >> rpt conj_tac
    >~ [`local_ptrs_reserved cenv s1`]
    >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]
    >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[])
    >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
        qexists_tac `sa` >> simp[])
    >~ [`gas_admissible _ _ _`]
    >- metis_tac[expr_body_pre_gas_admissible] >>
    `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
      metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)`
      (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
    qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
      qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
      qpat_assum `!fn i v. frag_reachable ctx func s0 fn i v ==> _`
        (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
         CONJ path o CONJ no_phi))))) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) childQ2 childR2` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[ec_source_tail_storage_frame] >>
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
  simp[exprSimHashTheory.expr_exit_INR_cast, exprSimDefsTheory.halt_exit_def]
QED

Resume ec_arith_vv_from_tail_full[second_success]:
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace)
      mid'.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?v2. res' = INL v2` by
    (asm_x "tail" kall_tac >> fs[Abbr `childQ2`] >> metis_tac[]) >>
  qpat_x_assum `res' = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v2` >> (conj_tac >- REFL_TAC) >> BETA_TAC >>
  `~t'.vs_halted /\ mid'.gas_obs = []` by
    (asm_x "tail" kall_tac >> metis_tac[]) >>
  asm "tail" irule >>
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

Theorem ec_arith_builtin_vv_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  match_mp_tac ec_arith_vv_from_tail_full >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL ec_arith_staged_cut) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==>
       gas_origin_ptr_path _ (t2,G2,tn2) [] (OK u,Gu,tnu) /\ _`
       (qspec_then `storage_trace_horizon es2.storage_trace`
         (drule_then strip_assume_tac)) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es2 u`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  Cases_on `u.vs_outcomes = []`
  >- (`gas_explicit [F] t2.vs_gas_readings = []` by
        (Cases_on `t2.vs_gas_readings` >> simp[gasSummaryTheory.gas_explicit_cons]) >>
      `w2n (64w:256 word) = 64` by
        simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
      qpat_assum `w2n (64w:256 word) = 64` (fn width =>
        qpat_assum `w2n wo + w2n (64w:256 word) <= _`
          (assume_tac o PURE_REWRITE_RULE [width])) >>
      W (fn (_,goal) =>
        let val normal_post = rand (rator goal) in
          mp_tac (INST [mk_var ("Q", type_of normal_post) |-> normal_post]
            (Q.INST [`tops` |-> `cx_tops cx`,
               `tys` |-> `[expr_type e1; expr_type e2]`,
               `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `rest` |-> `[ai]`]
               (SPEC_ALL ec_arith_empty_tail_full)))
        end) >>
      simp[] >>
      (impl_tac >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H _ ==>
          gas_origin_ptr_path _ (t2,G2,tn2) [] _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `w2n (64w:256 word) = 64` (fn width =>
          qpat_assum `ptr_covers Gu tnu dst u (w2n (64w:256 word))`
            (assume_tac o PURE_REWRITE_RULE [width])) >>
        qpat_assum `an = _` (fn width =>
          qpat_assum `ptr_covers Gu tnu src u (w2n an)`
            (assume_tac o PURE_REWRITE_RULE [width])) >>
        simp[])) >>
      disch_then ACCEPT_TAC) >>
  `vv = StackValue a (Var dst)` by
    simp[exprLoweringTheory.as_stack_val_def] >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= s2.cs_next_id` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
     qpat_assum `lower_value _ _ _ e2 s1 = _`
       (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
     simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom))) >> simp[]) >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom))) >> simp[]) >>
  `?obs1. es1.storage_trace = es.storage_trace ++ obs1` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     simp[storage_trace_frame_bind_all, storage_trace_frame_read_result,
          cj 5 evaluate_storage_trace_frame]) >>
  `?obs2. es2.storage_trace = es1.storage_trace ++ obs2` by
    (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `[]` (mp_then (Pos last) mp_tac storage_trace_frame_prefix)) >>
     simp[storage_trace_frame_bind_all, storage_trace_frame_read_result,
          cj 5 evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
    valid_horizon cx st0 H es1.storage_trace /\ valid_horizon cx st0 H es.storage_trace` by
    gvs[vyperStorageFootprintTheory.valid_horizon_def] >>
  rename1 `context$compile_alloc_buffer 64 out_alloc = (ob,sm)` >>
  mp_tac (SPEC_ALL ec_arith_permitted_tail_full) >>
  simp[] >>
  (impl_tac >- (conj_tac
    >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H _ ==>
          gas_origin_ptr_path _ (t2,G2,tn2) [] _ /\ _`
          (qspec_then `H` mp_tac) >> simp[] >> strip_tac >> simp[] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
    conj_tac
    >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H _ ==>
          expr_post H _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
          (qspec_then `H` mp_tac) >> simp[] >> strip_tac >> simp[]) >>
    gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==>
      expr_post H _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >> simp[] >> strip_tac >> simp[])) >>
  disch_then ACCEPT_TAC
QED

Theorem ec_arith_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a bt args) es` by
    (irule ec_arith_builtin_vv_sim_full >> simp[] >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  `a = ArrayT (BaseT (UintT 256)) (Fixed 2)` by
    (Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[ec_pre_types]) >>
  qpat_x_assum `a = ArrayT (BaseT (UintT 256)) (Fixed 2)` SUBST_ALL_TAC >>
  MATCH_MP_TAC (Q.INST
    [`rty` |-> `ArrayTV (BaseTV (UintT 256)) (Fixed 2)`]
    (SPEC_ALL expr_sim_full_of_vv)) >>
  simp[vyperASTTheory.expr_type_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def,
       compileEnvTheory.type_memory_bytes_def, valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >>
  `expr_body_pre cenv cx env
    (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bt args)
    (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >>
  simp[vyperASTTheory.expr_type_def, vyperValueTheory.evaluate_type_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >> metis_tac[]
QED
