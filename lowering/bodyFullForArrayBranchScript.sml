(* Source composition for the non-slot Array branch of For. *)
Theory bodyFullForArrayBranch
Ancestors
  bodyFullShadowBodyInv constSubst bodyStorageMetadata vyperSubscriptOverlap
  bodyFullForArrayRound gasOutcomeFull gasOutcomeFullCompose gasExemptCert
  gasContext gasSummary stmtSimForRounds stmtSimDefs exprSimDefs bodyPtrDefs
  haltExitProj vyperInterpreter vyperState vyperAST vyperValue
  vyperValueOperation vyperTyping vyperStorageTrace vyperStorageFootprint
  fragGasMode context venomExecSemantics list arithmetic
  bodySimFull bodyFullForFacts bodySim stmtLowering compileEnv emitHelper
  gasShadow supportedStmts exprSimHyps bodyExprPreFacts bodyFullForArray
  bodyFullShared gasOutcomeFullGuarded bodyFullForRounds vyperEvalExprPreservesScopesDom
  bodyFullIfExpReach contextRawReachable
  supportedExprTraverse[qualified,ignore_grammar]
  vyperTypeContract[qualified,ignore_grammar]

(* The loop continuation starts at the iterator's own captured endpoint. *)
Theorem for_nonslot_array_prefix_continue_full:
  evaluate_type (get_tenv cx) typ = SOME tyv /\ bound_length bd <= n /\
  gas_admissible (eval_stmt cx (For id typ (Array e) n loop_body)) (stmt_res_ok lctx) es /\
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_iterator cx (Array e)) (es,s,G,tn) P
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t)) /\
  (!H res em Gu tu u. P H res em Gu tu u ==>
    ?vs xs et av. res = INL vs /\ vs = MAP Value xs /\
      value_has_type (ArrayTV et bd) (ArrayV av) /\
      extract_elements (ArrayTV et bd) (ArrayV av) = SOME xs) /\
  (!marks vs em Gu tu u.
    (!tail. eval_iterator cx (Array e)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL vs,em with gas_obs := tail)) /\
    storage_trace_domain cx st0 em.storage_trace /\
    (!H. valid_horizon cx st0 H em.storage_trace ==> P H (INL vs) em Gu tu u) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK u,Gu,tu)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_for cx tyv id loop_body vs) (em,u,Gu,tu) Q
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==>
          !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==> allocas_below_fmp t))) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_stmt cx (For id typ (Array e) n loop_body)) (es,s,G,tn) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==>
        !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==> allocas_below_fmp t))
Proof
  strip_tac >>
  `eval_stmt cx (For id typ (Array e) n loop_body) =
    bind (eval_iterator cx (Array e))
      (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
        (eval_for cx tyv id loop_body vs))` by
    simp[Once evaluate_def, lift_option_type_def, bind_return] >>
  pop_assum SUBST_ALL_TAC >>
  irule gas_outcome_full_bind_all_path >> BETA_TAC >>
  conj_tac >-
    (gen_tac >> irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_checks, cj 4 evaluate_storage_trace_frame]) >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_bind_results >>
     goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_error_results >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[cj 3 evaluate_storage_trace_frame] >>
  qexists_tac `P` >> BETA_TAC >>
  reverse conj_tac >-
    (irule gas_outcome_full_post_mono >>
     qpat_assum `gas_outcome_full _ _ _ _ (eval_iterator _ _) _ _ _` (irule_at Any) >>
     simp[NoAsms] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_INL] >>
     strip_tac >> conj_tac
     >- (simp[stmt_exit_ptr_def] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
     conj_tac >- metis_tac[halt_exit_INR_type] >>
     rpt strip_tac >> gvs[] >> fs[expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `storage_trace_domain cx st0 em.storage_trace` >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  `P (storage_trace_horizon em.storage_trace) res em G1 tn1 t` by
    (first_x_assum irule >> simp[]) >>
  qpat_assum `!H res em Gu tu u. P H res em Gu tu u ==> _` drule >>
  strip_tac >> qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> conj_tac >- REFL_TAC >>
  `LENGTH vs <= n` by
    (Cases_on `bd` >> Cases_on `av` >>
     gvs[value_has_type_inv, extract_elements_def, array_elements_def,
         bound_length_def]) >>
  qpat_x_assum `vs = MAP Value xs` kall_tac >>
  `check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return ()` by
    simp[FUN_EQ_THM, compatible_bound_def, check_def, assert_def, return_def] >>
  `gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em` by
    (drule_all gas_admissible_bind_tail >>
     simp[ignore_bind_def, bind_return]) >>
  simp[ignore_bind_def, bind_return] >>
  first_x_assum irule >> conj_tac >- (qexists_tac `marks` >> simp[]) >>
  simp[return_def]
QED

Theorem nonslot_iterator_expr_pre[local]:
  body_inv tops ctx c cx /\ supported_iterator tops typ (Array e) n /\
  (!nid. e = TopLevelName (expr_type e) nid ==>
    IS_SOME (supported_immutable_type tops nid)) /\
  expr_type e = ArrayT typ bd /\ well_typed_iterator env typ (Array e) /\
  expr_sim_inv c cx env es /\ stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) ==>
  expr_body_pre c cx env e es
Proof
  strip_tac >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all bodySimTheory.body_inv_stmt_const_name_free >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          supportedStmtTraverseTheory.supported_iterator_exists_def]) >>
  `cx_tops cx = tops` by
    (irule gasContextTheory.cx_tops_module >>
     qpat_assum `body_inv tops ctx c cx` mp_tac >> simp[NoAsms,body_inv_def]) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env tops) target))` by
    (qpat_assum `body_inv tops ctx c cx` mp_tac >> simp[NoAsms,body_inv_def]) >>
  `well_typed_expr env e` by fs[vyperTypeSystemTheory.well_typed_iterator_def] >>
  `~expr_has_evm_run e /\
   EVERY (\c. FST c = NONE) (int_calls_expr e) /\
   EVERY (\c. IS_SOME (supported_function_decl tops c Internal)) (int_calls_expr e) /\
   ~is_extcode e /\ ~supported_expr_exists (const_name_root cx) e` suffices_by
    (strip_tac >>
     qpat_assum `stmt_exprs_ok c (For _ _ _ _ _)` mp_tac >>
     simp[NoAsms,stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def,
          allocLimitsTheory.alloc_limits_iterator_def,
          supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          supportedStmtTraverseTheory.supported_iterator_exists_def] >>
     strip_tac >>
     qspecl_then [`c`,`cx`,`env`,`e`,`es`,`int_calls_stmts loop_body`] mp_tac
       bodyExprPreFactsTheory.stmt_expr_body_pre_alloc >>
     impl_tac >- (
       simp[NoAsms] >>
       rpt (conj_tac >- first_assum ACCEPT_TAC) >>
       conj_tac >-
         (qpat_assum `call_evaluation_safe cx (int_calls_stmt _)` mp_tac >>
          simp[NoAsms,vyperTypeCallGraphTheory.int_calls_stmt_def,
               vyperTypeCallGraphTheory.int_calls_iterator_def]) >>
       rpt (conj_tac >- first_assum ACCEPT_TAC) >>
       conj_tac >-
         (strip_tac >> qexists_tac `tops` >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
       conj_tac >-
         (rpt strip_tac >> simp[] >> first_x_assum irule >>
          simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
               supportedStmtTraverseTheory.supported_iterator_exists_def]) >>
       fs[]) >>
     simp[]) >>
  `supported_expr tops e \/ (?ty name. e = Name ty name) \/ (?ty nid. e = TopLevelName ty nid)` by
    (qpat_assum `supported_iterator tops typ (Array e) n` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `e` >> simp[supported_iterator_def]) >>
  FIRST [
       (drule_then assume_tac supportedExprTraverseTheory.supported_expr_no_evm_run >>
        drule_then assume_tac bodyStorageCasesTheory.supported_expr_main_calls >>
        `~is_extcode e` by
          (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
           qexists_tac `c` >>
           fs[stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def,
              allocLimitsTheory.alloc_limits_iterator_def]) >>
        fs[EVERY_CONJ]),
       (qpat_assum `e = Name _ _` SUBST_ALL_TAC >>
        simp[cj 1 supportedExprTraverseTheory.expr_has_evm_run_thm,
             supportedExprTraverseTheory.supported_expr_exists_def,
             vyperTypeCallGraphTheory.int_calls_expr_def,
             exprSimHypsDefsTheory.const_name_root_def,exprLoweringTheory.is_extcode_def]),
       (qpat_assum `e = TopLevelName _ _` SUBST_ALL_TAC >>
        fs[cj 3 supportedExprTraverseTheory.expr_has_evm_run_thm,
           supportedExprTraverseTheory.supported_expr_exists_def,
           vyperTypeCallGraphTheory.int_calls_expr_def,exprLoweringTheory.is_extcode_def])
  ]
QED

Theorem array_constant_decl_mem[local]:
  !tops id. constant_decl id tops <=>
    ?vis init ty slot. MEM (VariableDecl vis (Constant init) id ty slot) tops
Proof
  Induct >> simp[constant_decl_def] >>
  Cases_on `h` >> simp[constant_decl_def] >>
  rename1 `VariableDecl vis mut name ty slot` >>
  Cases_on `mut` >> simp[constant_decl_def] >> metis_tac[]
QED

Theorem array_constant_name_in_lowering[local]:
  !tops acc name. constant_decl name tops ==>
    MEM name (MAP FST (module_consts_env tops acc))
Proof
  recInduct module_consts_env_ind >>
  simp[constant_decl_def, module_consts_env_def] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `module_consts_env rest acc'` >>
  qspecl_then [`rest`, `acc'`] strip_assume_tac module_consts_env_acc_prefix >>
  simp[Abbr `acc'`]
QED

Theorem nonslot_iterator_bare_immutable:
  body_inv tops ctx c cx /\
  supported_iterator tops typ (Array e) n /\
  expr_type e = ArrayT typ bd /\
  ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
             supported_storage_value tops nid (ArrayT typ bd)) /\
  ~supported_expr_exists (const_name_root cx) e ==>
  !nid. e = TopLevelName (expr_type e) nid ==>
    IS_SOME (supported_immutable_type tops nid)
Proof
  strip_tac >>
  `get_module_code cx NONE = SOME tops` by fs[bodySimTheory.body_inv_def] >>
  rpt strip_tac >>
  qpat_assum `e = TopLevelName _ _` SUBST_ALL_TAC >>
  gvs[supported_iterator_def,vyperASTTheory.expr_type_def] >>
  PairCases_on `nid` >>
  gvs[supportedDeclsTheory.supported_constant_type_def, AllCaseEqs(),
      supportedExprTraverseTheory.supported_expr_exists_def,
      exprSimHypsDefsTheory.const_name_root_def] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  drule_then assume_tac gasContextTheory.cx_tops_module >>
  fs[exprSimHypsDefsTheory.cx_const_name_def] >>
  metis_tac[array_constant_name_in_lowering, array_constant_decl_mem, supported_variable_decl_mem]
QED

Theorem compile_for_nonslot_array_frag_full:
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
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (For id typ (Array e) n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ (Array e) n body) ==>
       occurs_abi_decode_target target tops) /\
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
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
      (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[bodySimFullTheory.stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (For _ _ _ _ _) _ = _` mp_tac >>
  simp[loweringPostsTheory.stmt_env_def,declare_stmt_local_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_x_assum `cenv = cenv'` (SUBST_ALL_TAC o SYM) >>
  `compile_stmt cenv lctx ret_ty (For id typ (Array e) n body') sa = ((),sb)`
    by gvs[] >>
  `compile_stmt cenv lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body'))
     shadow_sa = ((),shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,loweringPostsTheory.stmt_env_def,declare_stmt_local_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     pairarg_tac >> simp[]) >>
  `cenv.ce_alloca_locals /\ supported_program tops /\
   get_module_code cx NONE = SOME tops` by fs[bodySimTheory.body_inv_def] >>
  drule_then strip_assume_tac bodyFullForFactsTheory.type_stmt_for_projection >>
  drule_then strip_assume_tac bodyFullForFactsTheory.supported_stmt_for_projection >>
  `?bd. expr_type e = ArrayT typ bd /\ bound_length bd = n` by
    (drule_then strip_assume_tac vyperTypeSystemTheory.type_stmt_for_array_bound >>
     simp[bound_length_def]) >>
  `!nid. e = TopLevelName (expr_type e) nid ==>
     IS_SOME (supported_immutable_type tops nid)` by
    (MATCH_MP_TAC (Q.INST [`c` |-> `cenv`, `bd` |-> `bd`, `n` |-> `n`,
                          `ctx` |-> `ctx`, `typ` |-> `typ`]
                     nonslot_iterator_bare_immutable) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`c` |-> `cenv`,`sty` |-> `typ`,`fty` |-> `typ`,
      `loop_body` |-> `body'`,`sa0` |-> `sa`,`shadow_sa0` |-> `shadow_sa`]
      bodyFullForArrayRoundTheory.for_nonslot_array_layout_full) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then
    [`vv`,`sbExpr`,`shadow_sbExpr`,`loc`,`len_op`,`saL`] strip_assume_tac) >>
  rename1 `for_nonslot_layout _ _ _ _ _ (saBod,_,_,_,_,_,_,_,_) _` >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule_then assume_tac exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env >>
     drule vyperTypeSystemTheory.assignable_type_well_formed >>
     simp[vyperTypeSystemTheory.well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  qpat_assum `!tenv s'' tyv t. _ ==> body_iterator_full_ok _ _`
    (qspecl_then [`get_tenv cx`,`es`,`tyv`,`es`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  disch_tac >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`c` |-> `cenv`,`loop_body` |-> `body'`]
        nonslot_iterator_expr_pre) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by
    (rpt strip_tac >>
     qpat_assum `ret_pc_ok cenv sa s0`
       (drule_then (ACCEPT_TAC o CONJUNCT1) o
        REWRITE_RULE [loweringPostsTheory.ret_pc_ok_def])) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule exprSimHypsTheory.expr_body_pre_vv_gas_admissible >> simp[]) >>
  mp_tac (Q.INST [`PG` |-> `PG`,`st0` |-> `st0`,`c` |-> `cenv`,
      `elem` |-> `typ`,`s` |-> `s0`,`G` |-> `G0`,`tn` |-> `tn0`,
      `sb` |-> `sbExpr`,`shadow_sb` |-> `shadow_sbExpr`,`sc` |-> `saL`]
      for_nonslot_array_prefix_full) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  drule_all_then (assume_tac o BETA_RULE)
    (Q.INST [`d` |-> `d`,`cenv` |-> `cenv`,`sa` |-> `sa`]
       bodyFullSharedTheory.gas_outcome_full_return_buf_allocas) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Final _` >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_iterator _ _) _
      (\H res ee G' tn' t. _ /\ (!bw cap. d = SOME (bw,cap) ==> _)) _`
    (fn th =>
      let
        val post = List.nth (snd (strip_comb (concl th)), 6)
        val rule = Q.INST [`loop_body` |-> `body'`,`s` |-> `s0`,
          `G` |-> `G0`,`tn` |-> `tn0`,`Q` |-> `Final`] for_nonslot_array_prefix_continue_full
      in
        mp_tac (BETA_RULE (INST [mk_var ("P",type_of post) |-> post] rule))
      end) >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- simp[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >-
      (rpt gen_tac >> strip_tac >> qexistsl_tac [`vs`,`xs`,`et`,`av`] >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    map_every qx_gen_tac [`marks`,`vs`,`em`,`Gu`,`tu`,`u`] >> strip_tac >>
    `body_for_full_ok cx tyv id body' vs` by
      (qpat_assum `!tenv s'' tyv t s'3' vs t' s'4' x t''. _ ==> body_for_full_ok _ _ _ _ _`
         (qspecl_then [`get_tenv cx`,`es`,`tyv`,`es`,
           `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`,
           `vs`,`em with gas_obs := []`,`em`,`()`,`em`] mp_tac) >>
       impl_tac >- (simp[lift_option_type_def, return_def] >> first_assum ACCEPT_TAC) >>
       disch_then ACCEPT_TAC) >>
    `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
      fs[storage_trace_domain_def] >>
    qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
      (?vss rv av xs et. INL vs = INL vss /\ _) /\ _`
      (qspec_then `storage_trace_horizon em.storage_trace` mp_tac) >>
    impl_tac >- first_assum ACCEPT_TAC >>
    disch_then (fn th =>
      assume_tac (CONJUNCT2 th) >>
      qx_choosel_then [`vss`,`rv`,`av`,`xs`,`et`]
        (map_every assume_tac o CONJUNCTS) (CONJUNCT1 th)) >>
    qpat_x_assum `INL vs = INL vss` (SUBST_ALL_TAC o SYM o SRULE []) >>
    `!H. valid_horizon cx st0 H em.storage_trace ==>
          stmt_state_rel H ctx func cenv cx em u /\
          storage_well_formed_on cx em (FST H) /\
          ghost_inv_at (DF H) lo d cenv cx em Gu tu u` by
      (gen_tac >> strip_tac >>
       qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
         (?vss rv av xs et. INL vs = INL vss /\ _) /\ _`
         (qspec_then `H` (drule_then strip_assume_tac)) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    `MAP FDOM em.scopes = MAP FDOM es.scopes` by
      (qpat_assum `?obs. !tail. eval_expr cx e _ = (INL rv,_)`
         (qx_choose_then `obs` (qspec_then `[]`
           (mp_tac o MATCH_MP vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom))) >>
       simp[EQ_SYM_EQ]) >>
    `?delta. em.storage_trace = es.storage_trace ++ delta` by
      (qpat_assum `!tail. eval_iterator cx (Array e) _ = (INL vs,_)`
         (qspec_then `[]` (fn replay =>
           mp_tac (MATCH_MP storage_trace_frame_prefix
             (CONJ (Q.SPECL [`cx`,`Array e`] (cj 3 evaluate_storage_trace_frame)) replay)))) >>
       simp[]) >>
    `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) es.storage_trace` by
      (irule valid_horizon_append >> qexists_tac `delta` >>
       qpat_assum `em.storage_trace = es.storage_trace ++ delta`
         (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
    `return_buf_sep d cenv em u` by
      (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
         (qspec_then `storage_trace_horizon em.storage_trace` (drule_then strip_assume_tac)) >>
       drule_all_then ACCEPT_TAC bodyFullSharedTheory.return_buf_sep_locals_kept) >>
    `!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_no_wrap inst t` by
      (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
         metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
       qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
         gas_origin_ptr_path _ (s0,G0,tn0) marks (OK u,Gu,tu)`
         (qspec_then `storage_trace_horizon em.storage_trace` mp_tac) >>
       (impl_tac >- first_assum ACCEPT_TAC) >>
       disch_then (fn path =>
         qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
           (fn phi =>
             qpat_assum `!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_no_wrap inst t`
               (fn nowrap => ACCEPT_TAC (MATCH_MP
                 bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_no_wrap
                 (LIST_CONJ [path,phi,nowrap])))))) >>
    mp_tac (Q.INST [`c` |-> `cenv`,`sty` |-> `typ`,`fty` |-> `typ`,
      `loop_body` |-> `body'`,`sa0` |-> `sa`,`shadow_sa0` |-> `shadow_sa`,
      `sa` |-> `saBod`,`es0` |-> `es`,`dtv` |-> `tyv`,`stv` |-> `et`]
      (SPEC_ALL bodyFullForArrayRoundTheory.for_nonslot_array_round_contracts)) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then (qx_choosel_then [`s`,`G`,`tn`,`Inv`,`Done`]
      (map_every assume_tac o CONJUNCTS)) >>
    irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
    conj_tac >- simp[cj 4 evaluate_storage_trace_frame] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl [`G`,`s`,`tn`] >>
    conj_tac >-
      (gen_tac >> strip_tac >>
       qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
          gas_origin_ptr_path _ (u,Gu,tu) [] (OK s,G,tn) /\ _`
         (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
    qabbrev_tac `Round = (\a. do v <- read_result cx a;
      push_scope_with_var id tyv v;
      finally (try (do eval_stmts cx body'; return F od)
                   handle_loop_exception) pop_scope od)` >>
    qabbrev_tac `Next = (\rs b. if b then return () else eval_for cx tyv id body' rs)` >>
    qabbrev_tac `Exit = (\H ex ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex) r /\
      (ctx_has_dalloca ctx ==> !t. (r = Halt t \/ ?ir. r = IntRet ir t) ==>
        allocas_below_fmp t))` >>
    `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_for cx tyv id body' vs) (em,s,G,tn)
      (\H res ee G1 tn1 t. res = INL () /\ Done H ee G1 tn1 t)
      (\H res ee gt r. ?ex. res = INR ex /\ Exit H ex ee gt r)` by
      (irule bodyFullForRoundsTheory.eval_for_rounds_full >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qexistsl [`Inv`,`Next`,`stmt_res_ok lctx`,`Round`] >>
       conj_tac >-
         (simp[Abbr `Round`,Abbr `Exit`] >> first_assum ACCEPT_TAC) >>
       conj_tac >-
         (rpt gen_tac >> strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_bool >>
          goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[]) >>
       conj_tac >-
         (rpt gen_tac >> strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_bool >>
          simp[]) >>
       conj_tac >- simp[Abbr `Round`] >>
       conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- simp[Abbr `Next`] >>
       conj_tac >-
         (gen_tac >> strip_tac >>
          qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==>
            gas_origin_ptr_path _ (u,Gu,tu) [] (OK s,G,tn) /\ _`
            (qspec_then `H` (drule_then (ACCEPT_TAC o CONJUNCT2)))) >>
       first_assum ACCEPT_TAC) >>
    irule gas_outcome_full_post_mono >>
    qpat_assum `gas_outcome_full _ _ _ _ (eval_for _ _ _ _ _) (em,s,G,tn) _ _` (irule_at Any) >>
    BETA_TAC >> conj_tac >-
      (rpt gen_tac >> strip_tac >>
       qpat_assum `res = INL ()` (fn th => simp[NoAsms,Abbr `Final`,th]) >>
       qpat_assum `!H ee G1 tn1 t. Done H ee G1 tn1 t ==> _`
         (drule_then strip_assume_tac) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    rpt gen_tac >> strip_tac >>
    qpat_assum `Exit _ _ _ _ _` mp_tac >>
    qpat_assum `res = INR ex` (fn th => simp[NoAsms,Abbr `Exit`,th]) >>
    strip_tac >> conj_tac >-
      (qpat_assum `halt_exit H cx ee (INR ex) r` (fn th =>
         MATCH_ACCEPT_TAC (MATCH_MP (iffLR haltExitProjTheory.halt_exit_INR_type) th))) >>
    qpat_assum `ctx_has_dalloca ctx ==> !t. _ ==> allocas_below_fmp t` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  disch_then ACCEPT_TAC
QED
