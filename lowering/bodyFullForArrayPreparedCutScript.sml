(* Compose an array For from a prepared iterator expression and its continuation. *)
Theory bodyFullForArrayPreparedCut
Ancestors
  bodyInvExecutionProps
  bodyFullForExprCut bodyFullForArray bodyFullForFacts bodyFullShadowBodyInv
  bodyFullIfExpReach bodyFullShared bodySimFull bodySim
  gasOutcomeFull gasOutcomeFullCompose gasContext stmtSimForRounds stmtSimDefs
  stmtLowering loweringPosts compileEnv gasShadow exprSimHyps emitHelper
  exprSimAbiDecodeEntryTyping vyperTypeSystem vyperInterpreter vyperState
  vyperStorageTrace vyperStorageFootprint vyperEvalExprPreservesScopesDom list
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]

Theorem for_array_prepared_expr_cut_frag_full:
  !cx id typ e n loop_body DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) /\
     eval_iterator cx (Array e) s'3' = (INL vs,t') /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' = (INL x,t'') ==>
     body_for_full_ok_mods mods exps cx tyv id loop_body vs) /\
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' = (INL tyv,t) ==>
     body_iterator_full_ok_mods mods exps cx (Array e)) /\
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  (!st0 sa sb sha shb s0 G0 tn0 vv se she bd tyv marks rv em G tn u.
     compile_stmt cenv lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
     compile_stmt (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body))
       sha = ((),shb) /\
     compile_expr cenv (expr_type e) e sa = (vv,se) /\
     compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
     gas_shadow_state sa sha /\ gas_shadow_state se she /\ gas_shadow_state sb shb /\
     gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
     ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
     MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
     fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
     fn_has_code sa se func /\ fn_has_code sha she shadow_func /\
     ci_mono sa se /\ ci_mono se sb /\
     cenv.ce_alloca_locals /\ local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
     ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
     expr_type e = ArrayT typ bd /\ bound_length bd = n /\
     evaluate_type (get_tenv cx) typ = SOME tyv /\
     expr_body_pre_mods mods cenv cx env e es /\
     (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
                             (INL rv,em with gas_obs := tail)) /\
     storage_trace_domain cx st0 em.storage_trace /\
     (!H. valid_horizon cx st0 H em.storage_trace ==>
        for_array_expr_endpoint (DF,lo,d,ctx,func) cenv cx e (es,sa,s0,G0,tn0)
          (vv,se) H rv em G tn u) /\
     (!H. valid_horizon cx st0 H em.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) marks (OK u,G,tn)) /\
     (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
     (!H. dead_lo_ok H (DF H) lo cenv cx) /\
     (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
     return_buf_frame d cenv se u /\ return_buf_sep d cenv em u /\
     alloca_frame cenv es sa s0 cenv em u /\
     gas_admissible
       (bind (array_iterator_results cx (expr_type e) rv)
         (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                          (eval_for cx tyv id loop_body vs))) (stmt_res_ok lctx) em /\
     (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                     (INL vs,em with gas_obs := tail)) /\
            check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
            body_for_full_ok_mods mods exps cx tyv id loop_body vs /\
            gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0
       (bind (array_iterator_results cx (expr_type e) rv)
         (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                          (eval_for cx tyv id loop_body vs)))
       (em,u,G,tn) (for_array_loop_post (DF,lo,d,ctx,func) cenv cx lctx (es,sa,s0,G0,tn0) sb)
       (for_array_loop_exit ctx cx RetQ)) ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (For id typ (Array e) n loop_body))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body)))
    (eval_stmt cx (For id typ (Array e) n loop_body)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (For _ _ _ _ _) _ = _` mp_tac >>
  simp[stmt_env_def,declare_stmt_local_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `cenv = cenv'` (SUBST_ALL_TAC o SYM) >>
  `compile_stmt cenv lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb)` by gvs[] >>
  `compile_stmt (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body))
     shadow_sa = ((),shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,stmt_env_def,declare_stmt_local_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def] >> pairarg_tac >> simp[]) >>
  `cenv.ce_alloca_locals` by
    (drule_then (MATCH_ACCEPT_TAC o MATCH_MP contract_inv_alloca_locals)
       body_inv_contract) >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  `?bd. expr_type e = ArrayT typ bd /\ bound_length bd = n` by
    (drule_then strip_assume_tac type_stmt_for_array_bound >> simp[]) >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule_then assume_tac abi_decode_inv_type_env >>
     drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `body_iterator_full_ok cx (Array e)` by
    (qpat_assum `!tenv s'' tyv t. _ ==> body_iterator_full_ok _ _` irule >>
     qexistsl [`es`,`es`,`get_tenv cx`,`tyv`] >> simp[lift_option_type_def,return_def]) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by
    (rpt strip_tac >> qpat_assum `ret_pc_ok cenv sa s0`
      (drule_then (ACCEPT_TAC o CONJUNCT1) o REWRITE_RULE [ret_pc_ok_def])) >>
  drule_all for_array_expr_compile_cuts >>
  disch_then (qx_choosel_then [`vv`,`se`,`she`] strip_assume_tac) >>
  drule_then assume_tac expr_body_pre_vv_gas_admissible >>
  suspend "compose"
QED

Resume for_array_prepared_expr_cut_frag_full[compose]:
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_stmt cx (For id typ (Array e) n loop_body)) (es,s0,G0,tn0)
     (for_array_loop_post (DF,lo,d,ctx,func) cenv cx lctx (es,sa,s0,G0,tn0) sb)
     (for_array_loop_exit ctx cx RetQ)` suffices_by
    (strip_tac >> irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
     BETA_TAC >> conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC for_array_loop_post_witness) >>
     rewrite_tac[for_array_loop_exit_def] >> rpt gen_tac >> disch_tac >>
     first_assum ACCEPT_TAC) >>
  irule for_array_expr_finish >>
  qexistsl [`cenv`,`d`,`lctx`,`sa`,`se`,`tyv`,`vv`] >>
  conj_tac >- suspend "normal" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule gas_outcome_full_post_source >>
  drule_all (Q.INST [`sb` |-> `se`,`PG` |-> `PG`] for_array_expr_prefix_full) >>
  disch_then (irule_at Any) >> simp[for_array_expr_endpoint_def] >>
  rpt gen_tac >> strip_tac >> qexists_tac `tv` >> simp[]
QED

Resume for_array_prepared_expr_cut_frag_full[normal]:
  map_every qx_gen_tac [`marks`,`rv`,`em`,`G`,`tn`,`u`] >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_endpoint _ _ _ _ _ _ H _ _ _ _ _`
    (qspec_then `H0` (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_endpoint_def]))) >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_expr cx e _ = _`
    (qspec_then `[]` (assume_tac o SRULE [])) >>
  drule_then (assume_tac o GSYM o SRULE []) eval_expr_preserves_scopes_dom >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (irule valid_horizon_append >>
     drule_at (Pat `f _ = _`) storage_trace_frame_prefix >>
     simp[cj 5 evaluate_storage_trace_frame] >> strip_tac >>
     qexists_tac `observations` >> fs[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `H0` (drule_then assume_tac)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi >> disch_then (qspec_then `func` mp_tac) >> simp[]) >>
  `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t` by
    (rpt gen_tac >> strip_tac >> irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     goal_assum (drule_at (Pat `gas_origin_ptr_path _ _ _ _`)) >>
     qexists_tac `fn` >> simp[] >> first_assum ACCEPT_TAC) >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) u` by
    (rpt gen_tac >> strip_tac >> irule return_buf_allocas_path >>
     goal_assum (drule_at (Pat `gas_origin_ptr_path _ _ _ _`)) >>
     qexistsl [`cenv`,`d`,`es`,`sa`] >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv em u` by
    (drule_all vv_post_alloca_frame >> simp[EQ_SYM_EQ]) >>
  qhdtm_assum `vv_post` (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `return_buf_sep d cenv em u` by (drule_all return_buf_sep_locals_kept >> simp[]) >>
  `return_buf_frame d cenv se u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
     fs[exprLoweringPropsTheory.ci_mono_def]) >>
  qpat_assum `!st0 sa sb sha shb s0 G0 tn0 vv se she bd tyv marks rv em G tn u. _` irule >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "loop_ih"
QED

Resume for_array_prepared_expr_cut_frag_full[loop_ih]:
  conj_tac >-
    (gen_tac >> strip_tac >>
     conj_tac >-
       (`eval_iterator cx (Array e)
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL vs,em)` by
          (simp[Once evaluate_def,bind_def] >>
           qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
           simp[] >> metis_tac[]) >>
        `lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" es = (INL tyv,es)` by
          simp[lift_option_type_def,return_def] >>
        qpat_assum `!tenv s'' tyv t s'3' vs t' s'4' x t''. _ ==> body_for_full_ok _ _ _ _ _`
          (qspec_then `get_tenv cx` (drule_all o SRULE [])) >> simp[]) >>
     `check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return ()` by
       fs[check_def,assert_def,return_def,raise_def,FUN_EQ_THM] >>
     drule_all (Q.INST [`xs` |-> `[]`] gas_admissible_bind_tail |> SRULE []) >>
     simp[ignore_bind_def,bind_return]) >>
  conj_tac >- (qexists_tac `marks` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (qexists_tac `bd` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexistsl [`se`,`shadow_sa`,`shadow_sb`,`she`,`vv`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise for_array_prepared_expr_cut_frag_full
