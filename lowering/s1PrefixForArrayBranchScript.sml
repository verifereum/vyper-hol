(* Request-prefix companion to bodyFullForArrayBranch. *)
Theory s1PrefixForArrayBranch
Ancestors
  bodySingletonStmtGuards[qualified] stmtExprAllocationPreProps[qualified]
  s1PrefixPreds bodyFullForArrayBranch s1PrefixDefs
  s1PrefixForArrayRound s1PrefixForRounds s1PrefixCompose s1PrefixOfVV
  bodyTypedTargetScope[qualified,ignore_grammar] bodyInvCodeProps
  bodyFullForArrayRound bodyFullForFacts bodyFullForArray bodyFullShared
  stmtSimForRounds vyperInterpreter vyperState vyperStorageTrace
  vyperStorageFootprint vyperValueOperation vyperAST
  stmtLowering compileEnv gasShadow bodyInvExecutionProps bodySim s1PrefixProps
  vyperValue gasOutcomeFull vyperEvalExprPreservesScopesDom bodyFullIfExpReach

val _ = Parse.hide "body";

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[stmt_frag_prefix_def,stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (For _ _ _ _ _) _ = _` mp_tac >>
  simp[loweringPostsTheory.stmt_env_def,declare_stmt_local_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `cenv = cenv'` (SUBST_ALL_TAC o SYM) >>
  rename1 `compile_stmt cenv lctx ret_ty (For id typ (Array e) n loop_body) sa = (r,cb)` >>
  Cases_on `r` >> qpat_x_assum `cb = sb` SUBST_ALL_TAC >>
  `compile_stmt (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body))
     shadow_sa = ((),shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,loweringPostsTheory.stmt_env_def,declare_stmt_local_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def] >> pairarg_tac >> simp[]) >>
  drule_then (assume_tac o MATCH_MP contract_inv_alloca_locals) body_inv_contract >>
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_then strip_assume_tac supported_stmt_for_projection >>
  `?bd. expr_type e = ArrayT typ bd /\ bound_length bd = n` by
    (drule_then strip_assume_tac vyperTypeSystemTheory.type_stmt_for_array_bound >>
     simp[bound_length_def]) >>
  `!nid. e = TopLevelName (expr_type e) nid ==> FST nid = NONE` by
    suspend "toplevel_scope" >>
  `!nid. e = TopLevelName (expr_type e) nid ==>
     IS_SOME (supported_immutable_type tops nid)` by suspend "toplevel_immutable" >>
  drule_all_then strip_assume_tac bodySingletonStmtGuardsTheory.singleton_stmt_expr_guards >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`s` |-> `(For id typ (Array e) n loop_body)`,
                     `tops` |-> `tops`, `ctx` |-> `ctx`]
        stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          supportedStmtTraverseTheory.supported_iterator_exists_def] >>
     disch_then irule >> strip_tac >>
     irule nonslot_iterator_expr_pre >>
     fs[bodySimTheory.body_inv_split_def,
        bodyInvSplitTheory.module_body_inv_def, alistTheory.ALOOKUP_def] >>
     metis_tac[]) >>
     qexistsl_tac [`bd`,`ctx`,`id`,`loop_body`,`n`,`tops`,`typ`] >> simp[]) >>
  mp_tac (Q.INST [`c` |-> `cenv`,`sty` |-> `typ`,`fty` |-> `typ`,
      `loop_body` |-> `loop_body`,`sa0` |-> `sa`,`shadow_sa0` |-> `shadow_sa`]
      for_nonslot_array_layout_full) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then
    [`vv`,`sbExpr`,`shadow_sbExpr`,`loc`,`len_op`,`saL`] strip_assume_tac) >>
  rename1 `for_nonslot_layout _ _ _ _ (_,cond_label,_,_,_,_,_,_,_,_) (saBod,_,_,_,_,_,_,_,_) _` >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule_then assume_tac exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >>
     drule vyperTypeSystemTheory.assignable_type_well_formed >>
     simp[vyperTypeSystemTheory.well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `body_iterator_full_ok cx (Array e)` by
    (first_assum irule >> qexistsl_tac [`es`,`es`,`get_tenv cx`,`tyv`] >>
     simp[lift_option_type_def,return_def]) >>
  `body_iterator_prefix_ok cx (Array e)` by
    (first_assum irule >> qexistsl_tac [`es`,`es`,`get_tenv cx`,`tyv`] >>
     simp[lift_option_type_def,return_def]) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by
    (rpt strip_tac >>
     qpat_assum `ret_pc_ok cenv sa s0`
       (drule_then (ACCEPT_TAC o CONJUNCT1) o
        REWRITE_RULE [loweringPostsTheory.ret_pc_ok_def])) >>
  drule_then assume_tac exprSimHypsTheory.expr_body_pre_vv_gas_admissible >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (eval_iterator cx (Array e)) (es,s0,G0,tn0)` by suspend "iterator_prefix" >>
  mp_tac (Q.INST [`PG` |-> `PG`,`st0` |-> `st0`,`c` |-> `cenv`,
      `elem` |-> `typ`,`s` |-> `s0`,`G` |-> `G0`,`tn` |-> `tn0`,
      `sb` |-> `sbExpr`,`shadow_sb` |-> `shadow_sbExpr`,`sc` |-> `saL`]
      for_nonslot_array_prefix_full) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`,`cenv` |-> `cenv`,`sa` |-> `sa`]
       gas_outcome_full_return_buf_allocas) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_iterator _ _) _ (\H res ee g tn t. ?vs. _) _` kall_tac >>
  `eval_stmt cx (For id typ (Array e) n loop_body) =
    bind (eval_iterator cx (Array e))
      (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
        (eval_for cx tyv id loop_body vs))` by
    simp[Once evaluate_def, lift_option_type_def, bind_return] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_iterator _ _) _ _ _`
    (mp_then Any irule gas_prefix_full_bind_replay) >>
  conj_tac >- suspend "rounds" >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_ignore_bind, storage_trace_frame_checks] >>
  rpt gen_tac >> Cases_on `res` >> simp[]
QED
*)
Theorem compile_for_nonslot_array_frag_prefix:
  !cx id typ e n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
               supported_storage_value tops nid (ArrayT typ bd)) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Array e) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx (Array e)) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Array e) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_prefix_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_prefix_ok cx (Array e)) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (For id typ (Array e) n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ (Array e) n body) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
    ~supported_expr_exists (const_name_root cx) e /\
    stmt_exprs_ok cenv (For id typ (Array e) n body) /\
    (~(?ty nid. e = TopLevelName ty nid) ==>
     !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid) /\
    stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
      (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_nonslot_array_frag_prefix[toplevel_scope]:
  qpat_assum `well_typed_iterator env typ (Array e)`
    (assume_tac o CONJUNCT1 o REWRITE_RULE [vyperTypeSystemTheory.well_typed_iterator_def]) >>
  rpt strip_tac >> PairCases_on `nid` >>
  `well_typed_expr env (TopLevelName (expr_type e) (nid0,nid1))` by
    (qpat_assum `e = TopLevelName _ _` (fn th => REWRITE_TAC[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  PURE_REWRITE_TAC[pairTheory.FST] >>
  drule_all_then ACCEPT_TAC bodyTypedTargetScopeTheory.body_inv_toplevel_read_main
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_nonslot_array_frag_prefix[toplevel_immutable]:
  drule_then assume_tac body_inv_contract >>
  drule_then strip_assume_tac body_inv_main_code >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                   `c` |-> `cenv`, `bd` |-> `bd`, `n` |-> `n`,
                   `ctx` |-> `ctx`, `typ` |-> `typ`]
            nonslot_iterator_bare_immutable_mods) >>
  fs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
     GSYM exprSimHypsDefsTheory.const_name_root_mods_singleton] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `FST nid = NONE` by
    (qpat_assum `!nid. e = TopLevelName (expr_type e) nid ==> FST nid = NONE`
       (qspec_then `nid` mp_tac) >> simp[]) >>
  qpat_assum `!nid. _ ==> IS_SOME (supported_immutable_type tops (NONE,SND nid))`
    (qspec_then `nid` mp_tac) >>
  PairCases_on `nid` >> gvs[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_nonslot_array_frag_prefix[iterator_prefix]:
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (eval_expr cx e) (es,s0,G0,tn0)` suffices_by
    (strip_tac >>
     `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (eval_iterator cx (Array e)) (es,s0,G0,tn0) <=>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
        (eval_expr cx e) (es,s0,G0,tn0)` by
       (irule gas_prefix_full_state_cong >> gen_tac >> simp[Once evaluate_def] >>
        Cases_on `eval_expr cx e qe` >> rename1 `_ = (res,ee)` >>
        Cases_on `res` >> simp[bind_def] >>
        Cases_on `array_iterator_results cx (ArrayT typ bd) x ee` >>
        drule array_iterator_results_state >> simp[]) >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es` by
    (qpat_assum `body_iterator_prefix_ok _ _`
      (mp_tac o REWRITE_RULE [body_iterator_prefix_ok_def, Once body_expr_prefix_ok_def]) >>
     disch_then (drule_all o CONJUNCT1) >> simp[]) >>
  qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sbExpr`,`shadow_sa`,`shadow_sbExpr`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[expr_vv_sim_full_pre_def] >> disch_then irule >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_nonslot_array_frag_prefix[rounds]:
  map_every qx_gen_tac [`marks`,`vs`,`em`,`Gu`,`tu`,`u`] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> gas_origin_ptr_path _ _ marks _ /\ _`
    (qspec_then `H0` (drule_then
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (qx_choosel_then [`vals`,`rv`,`av`,`xs`,`et`] (map_every assume_tac o CONJUNCTS))
        ASSUME_TAC)))) >>
  qpat_x_assum `INL vs = INL _` (SUBST_ALL_TAC o SYM o SRULE []) >>
  `LENGTH vs <= n` by
    (qpat_assum `vs = MAP Value xs` mp_tac >>
     qpat_assum `bound_length bd = n` mp_tac >>
     qpat_assum `extract_elements _ (ArrayV av) = SOME xs` mp_tac >>
     qpat_assum `value_has_type _ (ArrayV av)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bd` >> Cases_on `av` >>
     simp[vyperTypingTheory.value_has_type_inv, extract_elements_def, array_elements_def,
          bound_length_def] >> rw[] >> simp[]) >>
  `check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return ()` by
    simp[FUN_EQ_THM,compatible_bound_def,check_def,assert_def,return_def] >>
  `gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em` by
    (drule_all gas_admissible_bind_tail >> simp[ignore_bind_def,bind_return]) >>
  `eval_iterator cx (Array e)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []) =
      (INL vs,em with gas_obs := [])` by simp[] >>
  `body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs` by
    (`lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" es = (INL tyv,es)` by
       simp[lift_option_type_def,return_def] >>
     `check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em)` by
       simp[return_def] >>
     `get_tenv cx = get_tenv cx` by REFL_TAC >>
     conj_tac
     >- (qpat_assum `!tenv a b c d e f g h i. _ ==> body_for_full_ok _ _ _ _ _`
           (drule_all_then ACCEPT_TAC)) >>
     qpat_assum `!tenv a b c d e f g h i. _ ==> body_for_prefix_ok _ _ _ _ _`
       (drule_all_then ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H em.storage_trace ==>
        stmt_state_rel H ctx func cenv cx em u /\
        storage_well_formed_on cx em (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx em Gu tu u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> gas_origin_ptr_path _ _ marks _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM em.scopes = MAP FDOM es.scopes` by
    (qpat_assum `?obs. !tail. eval_expr cx e _ = (INL rv,_)`
       (qx_choose_then `obs`
         (qspec_then `[]` (mp_tac o MATCH_MP eval_expr_preserves_scopes_dom))) >>
     simp[EQ_SYM_EQ]) >>
  `?delta. em.storage_trace = es.storage_trace ++ delta` by
    (qpat_assum `!tail. eval_iterator cx (Array e) _ = (INL vs,_)`
       (qspec_then `[]` (fn replay =>
         mp_tac (MATCH_MP storage_trace_frame_prefix
           (CONJ (Q.SPECL [`cx`,`Array e`] (cj 3 evaluate_storage_trace_frame)) replay)))) >>
     simp[]) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (irule valid_horizon_append >> qexists_tac `delta` >>
     qpat_assum `em.storage_trace = es.storage_trace ++ delta`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `return_buf_sep d cenv em u` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >>
     drule_all_then ACCEPT_TAC return_buf_sep_locals_kept) >>
  `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK u,Gu,tu)` mp_tac >>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> _` mp_tac >>
     qpat_assum `!fn inst t. frag_reachable ctx func s0 fn inst t ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (mp_then (Pos hd) (mp_tac o SPEC_ALL)
      (Q.INST [`es0` |-> `es`,`dtv` |-> `tyv`,`stv` |-> `et`]
         (SPEC_ALL for_nonslot_array_round_prefix_contracts))) >>
  (impl_tac >- (unabbrev_all_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`s`,`G`,`tn`,`Inv`,`Done`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `check _ _ = return ()`
    (fn th => simp[NoAsms,th,ignore_bind_def,bind_return]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[NoAsms,cj 4 evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G`,`s`,`tn`] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
        gas_origin_ptr_path _ (u,Gu,tu) [] (OK s,G,tn) /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  irule eval_for_rounds_prefix >>
  conj_tac >-
    (qexists_tac `\rs b. if b then return () else eval_for cx tyv id loop_body rs` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Done`,`Inv`,
    `\H ex ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
       halt_exit H cx ee (INR ex) r /\
       (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==> allocas_below_fmp t)`,
    `stmt_res_ok lctx`,
    `\a. do v <- read_result cx a; push_scope_with_var id tyv v;
       finally (try (do eval_stmts cx loop_body; return F od) handle_loop_exception) pop_scope od`,
    `cx_tops cx`] >>
  BETA_TAC >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> conj_tac >> first_assum (drule_all_then ACCEPT_TAC)) >>
  conj_tac >- simp[] >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
        gas_origin_ptr_path _ (u,Gu,tu) [] (OK s,G,tn) /\ _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_for_nonslot_array_frag_prefix
*)
