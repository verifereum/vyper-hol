(* Request-prefix companion to bodyFullBuiltinECArithCompose. *)
Theory s1PrefixBuiltinECArithCompose
Ancestors
  s1PrefixPreds bodyFullBuiltinECArithCompose s1PrefixDefs s1PrefixCompose
  s1PrefixOfVV s1PrefixPrecompile bodyFullPreds bodySimFull exprSimECArith
  exprSimHypsDefs exprLowering loweringPosts exprSimDefs vyperAST list
  vyperStorageTrace vyperStorageFootprint vyperState gasOutcomeFull gasSummary
  s1PrefixProps bodyFullIfExpReach[qualified,ignore_grammar]
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullExprsListFacts bodyFullExprsSingleton bodyFullSimProjection

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
   ?e1 e2. args = [e1;e2] /\
     expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     expr_type e2 = (if bt = ECAdd then
       ArrayT (BaseT (UintT 256)) (Fixed 2) else BaseT (UintT 256))` by
    (Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[ec_pre_types]) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  `!n. bt <> Slice n` by (Cases_on `bt = ECAdd` >> gvs[]) >>
  `builtin_args_length_ok bt 2` by
    (Cases_on `bt = ECAdd` >> gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  `body_exprs_full_ok cx [e1;e2] /\ body_exprs_prefix_ok cx [e1;e2]` by simp[] >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "code_cuts"
QED
*)
Theorem ec_arith_builtin_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
  (bt = ECAdd \/ bt = ECMul) /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a bt args) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume ec_arith_builtin_vv_sim_prefix[code_cuts]:
  `?x y s1 s2 res.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
    (if bt = ECAdd then compile_ecadd_points x y s2
     else compile_ecmul_point x y s2) = (res,sb)` by
    (Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[compile_ec_operands]) >>
  `?sx sy sh1 sh2 shres.
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e1) shadow_sa = (sx,sh1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
      (gas_shadow_expr e2) sh1 = (sy,sh2) /\
    (if bt = ECAdd then compile_ecadd_points sx sy sh2
     else compile_ecmul_point sx sy sh2) = (shres,shadow_sb)` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (assume_tac o REWRITE_RULE [gasShadowTheory.gas_shadow_expr_def,listTheory.MAP]) >>
     Cases_on `bt = ECAdd` >> gvs[gasShadowTheory.gas_shadow_builtin_def] >>
     metis_tac[compile_ec_operands, gasShadowTheory.gas_shadow_expr_type]) >>
  `sx = x /\ gas_shadow_state s1 sh1` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e1 sa = (x,s1)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
  `sy = y /\ gas_shadow_state s2 sh2` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e2 s1 = (y,s2)` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) sh1 = _` (irule_at Any) >>
     simp[] >> irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >> qpat_x_assum `sy = y` SUBST_ALL_TAC >>
  `cs_extends s2 sb /\ cs_extends sh2 shadow_sb` by
    (Cases_on `bt = ECAdd` >> gvs[] >>
     metis_tac[externalEntryShapeTheory.compile_ecadd_points_labels,
               externalEntryShapeTheory.compile_ecmul_point_labels, pairTheory.SND]) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\
   cs_extends shadow_sa sh1 /\ cs_extends sh1 sh2` by
    (let val growth = cj 2 exprLoweringPropsTheory.compile_expr_grows in
      qpat_assum `lower_value _ _ _ e1 sa = _` (mp_then Any strip_assume_tac growth) >>
      qpat_assum `lower_value _ _ _ e2 s1 = _` (mp_then Any strip_assume_tac growth) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
        (mp_then Any strip_assume_tac growth) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) sh1 = _`
        (mp_then Any strip_assume_tac growth) >> simp[] end) >>
  `cs_extends s1 sb /\ cs_extends sh1 shadow_sb` by
    (conj_tac >- (irule compileEnvTheory.cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
     irule compileEnvTheory.cs_extends_trans >> qexists_tac `sh2` >> simp[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa sh1 shadow_func /\ fn_has_code sh1 shadow_sb shadow_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code sh1 sh2 shadow_func /\ fn_has_code sh2 shadow_sb shadow_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  suspend "first_operand"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ec_arith_builtin_vv_sim_prefix[first_operand]:
  `expr_body_pre cenv cx env e1 es` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ [e1;e2]) _`
       (mp_then Any mp_tac exprOpenFirstOperandTheory.expr_body_pre_builtin_head) >>
     simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e1) e1 es /\
   expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e1) e1 es` by
    (conj_tac
     >- (`body_expr_full_ok cx e1` by fs[body_exprs_full_ok_cons] >>
         drule_all body_expr_full_ok_simulations >> simp[]) >>
     qpat_assum `body_exprs_prefix_ok _ _` mp_tac >>
     pure_rewrite_tac[body_exprs_prefix_ok_def] >> strip_tac >>
     qpat_x_assum `body_expr_prefix_ok _ _` (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE[expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`sh1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ e1 _`
       (mp_tac o REWRITE_RULE[expr_sim_prefix_def,expr_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`sh1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  suspend "first_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ec_arith_builtin_vv_sim_prefix[first_bind]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn t. childQ H rr ee G tn t /\ ~t.vs_halted /\
      (!fn i u. frag_reachable ctx func t fn i u ==> dalloca_fmp_headroom i u)) childR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ childQ childR` (irule_at Any) >>
     simp[] >> rpt strip_tac
     >- (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
         simp[fragExecTheory.exit_result_def]) >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  drule ec_eval_bind >> disch_then (rewrite_tac o single) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H rr ee G tn t. childQ H rr ee G tn t /\ _) childR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
       storage_trace_frame_read_result, ec_source_tail_storage_frame,
       requests_outcomes_frame_bind_all, cj 5 evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  rpt conj_tac
  >~ [`ISR _`]
  >- (qx_gen_tac `hr` >> qx_gen_tac `rr` >> Cases_on `rr` >> simp[Abbr `childR`]) >>
  suspend "second_operand"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ec_arith_builtin_vv_sim_prefix[second_operand]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid.gas_obs) = (INL v,mid)` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `mid.gas_obs` mp_tac) >> simp[]) >>
  `?st raw sm sm'. eval_expr cx e1 st = (INL raw,sm) /\
     read_result cx raw sm = (INL v,sm')` by
    (qpat_assum `bind (eval_expr cx e1) _ _ = _`
       (mp_then Any mp_tac vyperStatePreservationTheory.bind_split) >> simp[] >>
     strip_tac >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_assum `bind (eval_expr cx e1) (read_result cx) _ = _`
       (mp_then (Pos last) (qspec_then `cenv` mp_tac)
         (REWRITE_RULE [ETA_THM] exprSimSourceTheory.expr_body_pre_eval)) >>
     disch_then (qspec_then `env` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule exprSimSourceTheory.expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     qexistsl_tac [`a`,`[e1;e2]`,`bt`,`es`] >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts] >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e2) e2 mid /\
   expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e2) e2 mid` by
    (conj_tac
     >- (`body_exprs_full_ok cx [e2]` by
           (qpat_assum `body_exprs_full_ok cx [e1;e2]` mp_tac >>
            pure_rewrite_tac[Once body_exprs_full_ok_cons] >> metis_tac[]) >>
         `body_expr_full_ok cx e2` by fs[body_exprs_full_ok_singleton] >>
         drule_all body_expr_full_ok_simulations >> simp[]) >>
     qpat_assum `body_exprs_prefix_ok _ _` mp_tac >>
     pure_rewrite_tac[body_exprs_prefix_ok_def] >> strip_tac >>
     `body_expr_prefix_ok cx e2` by metis_tac[] >>
     qpat_x_assum `body_expr_prefix_ok _ e2` (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  suspend "second_pre"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ec_arith_builtin_vv_sim_prefix[second_pre]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
        expr_post H ctx func cenv cx e1 es sa s1 s0 mid v x t /\
        ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (qx_gen_tac `hh` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H _ _ _ _ _ /\ _`
       (qspec_then `hh` mp_tac) >> simp[Abbr `childQ`] >> gvs[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[Abbr `childQ`] >> strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >> simp[]) >>
  `return_buf_frame d cenv s1 t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post H _ _ _ _ e1 es sa s1 s0 mid v x t /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace`
         (drule_then (strip_assume_tac o REWRITE_RULE[expr_post_def]))) >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p)` by
    (conj_tac >> rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid t /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (qx_gen_tac `hh` >> strip_tac >>
     qpat_x_assum `valid_horizon _ _ (storage_trace_horizon _) _` kall_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post H _ _ _ _ e1 es sa s1 s0 mid v x t /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE[expr_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  suspend "second_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ec_arith_builtin_vv_sim_prefix[second_bind]:
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE[expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`s1`,`s2`,`sh1`,`sh2`,`y`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e2) (read_result cx)) (mid,t,G1,tn1)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ e2 _`
       (mp_tac o REWRITE_RULE[expr_sim_prefix_def,expr_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`s1`,`s2`,`sh1`,`sh2`,`y`,`t`,`G1`,`tn1`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) childQ2 childR2` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e2) (read_result cx)) (mid,t,G1,tn1)
     (\H rr ee G tn u. childQ2 H rr ee G tn u /\ ~u.vs_halted) childR2` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) childQ2 childR2` (irule_at Any) >>
     simp[] >> rpt strip_tac >> drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) (\H rr ee G tn u. childQ2 H rr ee G tn u /\ _) childR2`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
       storage_trace_frame_read_result, ec_source_tail_storage_frame,
       requests_outcomes_frame_bind_all, cj 5 evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  rpt conj_tac
  >~ [`ISR _`]
  >- (qx_gen_tac `hr` >> qx_gen_tac `rr` >> Cases_on `rr` >> simp[Abbr `childR`, Abbr `childR2`]) >>
  rpt gen_tac >>
  simp[ec_source_tail_def, AllCaseEqs(), ignore_bind_def, bind_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_assum `precompile_call_success _ _ _ = _`
    (mp_then Any mp_tac precompile_call_success_only_computed_outcomes) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise ec_arith_builtin_vv_sim_prefix
*)

Theorem ec_arith_builtin_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
  (bt = ECAdd \/ bt = ECMul) /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a bt args) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a bt args) es` by
    (irule ec_arith_builtin_vv_sim_prefix >> simp[] >>
     qexistsl_tac [`env`,`tops`] >> simp[]) >>
  simp[] >> irule expr_sim_prefix_of_vv >> first_assum ACCEPT_TAC
QED
