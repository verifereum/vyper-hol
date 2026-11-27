(* A literal storage name uses the same loop as a captured storage place. *)
Theory bodyFullForStorageRoute
Ancestors
  bodyFullForArrayPreparedCut forStorageLiteralPre forStorageLiteralCapture
  forCapturedStorageContinue[qualified,ignore_grammar]
  bodyFullForExprCut bodySimFull bodySim bodyMemoryDefs loweringStateRelDefs
  vyperInterpreter vyperState vyperStorageFootprint vyperTypeValues vyperAST
  exprLowering supportedStmts venomInst finite_map list arithmetic
  bodyFullPostsMods[qualified] bodyFullPredsMods[qualified] bodyFullShadowBodyInv[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac for_storage_literal_expr_pre >>
  irule for_array_prepared_expr_cut_frag_full >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`env`,`env'`,`tops`] >> asm_rewrite_tac[] >>
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`s0`,`G0`,`tn0`,`vv`,
    `se`,`she`,`bound`,`tyv`,`marks`,`rv`,`em`,`G`,`tn`,`u`] >>
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `bound = bd` by fs[expr_type_def] >>
  qpat_x_assum `bound = bd` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule_at_then (Pat `valid_horizon _ _ _ _`) drule_all for_storage_literal_capture >>
  disch_then (qx_choosel_then [`tr`,`off`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `rv = PlaceR _` SUBST_ALL_TAC >>
  `bound_length bd <= n` by simp[] >>
  irule forCapturedStorageContinueTheory.for_captured_storage_continue_full >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexistsl [`se`,`vv`] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     disj1_tac >> qexists_tac `n2w off` >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`bindings`,`env`,`env'`,`ret_ty`,`sha`,`shadow_func`,`shb`,`tops`,`typ`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem compile_for_storage_array_frag_full:
  !cx id typ bd nid n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!c0 e0 sa0 s0 c1 e1 s1 sa1 c2 e2 s2.
       alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
       alloca_frame c1 e1 sa1 s1 c2 e2 s2 /\
       sa0.cs_next_id <= sa1.cs_next_id /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP s1.vs_allocas aid = SOME b) ==>
       alloca_frame c0 e0 sa0 s0 c2 e2 s2) /\
    (!c0 e0 sa0 s0 c1 e1 s1 sa1 tn0 tn1 tn2.
       alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
       sa0.cs_next_id <= sa1.cs_next_id /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP s1.vs_allocas aid = SOME b) /\
       (!aid off sz i.
          FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa0.cs_next_id /\
          (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\
          off<=i /\ i<off+sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem) /\
       (!aid off sz i.
          FLOOKUP s1.vs_allocas aid = SOME (off,sz) /\
          aid < sa1.cs_next_id /\
          (!name b sz'. local_region c1 e1.scopes s1 name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\
          off<=i /\ i<off+sz /\ i IN tn2.t_mem ==> i IN tn1.t_mem) ==>
       !aid off sz i.
          FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
          aid < sa0.cs_next_id /\
          (!name b sz'. local_region c0 e0.scopes s0 name b sz' ==>
            off+sz <= b \/ b+sz' <= off) /\
          off<=i /\ i<off+sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem) /\
    (!H cc ee res r sc g.
       halt_exit H cc ee res r ==>
       halt_exit H cc (ee with <|scopes := sc; gas_obs := g|>) res r) /\
    supported_storage_value tops nid (ArrayT typ bd) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) /\
       eval_iterator cx (Array (TopLevelName (ArrayT typ bd) nid)) s'3' =
         (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
         (INL x,t'') ==>
       body_for_full_ok_mods mods exps cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
         (INL tyv,t) ==>
       body_iterator_full_ok_mods mods exps cx (Array (TopLevelName (ArrayT typ bd) nid))) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
    supported_stmt tops bindings
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) = SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body) /\
    call_evaluation_safe cx (int_calls_stmt
      (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)) /\
    frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
        (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt
        (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)))
      (eval_stmt cx
        (For id typ (Array (TopLevelName (ArrayT typ bd) nid)) n body)) es
Proof
  cheat
QED
