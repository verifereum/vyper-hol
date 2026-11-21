(* Continuation of a storage-array For after evaluating its iterator place. *)
Theory forCapturedStorageContinue
Ancestors
  bodyFullForExprCut bodyFullForArrayRound bodyFullForRounds bodyFullForFacts
  forCapturedStorageCode forCapturedStorageEntry forCapturedStorageHead forCapturedStorageRound
  bodyFullForStorage bodyFullForStorageCapture bodyFullForRange bodyFullIfExpReach
  bodyFullShared bodySim bodySimFull bodyFullPreds bodyFullShadowBodyInv
  exprSimSource exprSimHyps exprSimProps exprSimHypsDefs exprSimCopy loweringPosts
  loweringStateRelDefs stmtSimDefs stmtSimProps bodyPtrDefs bodyMemoryDefs
  bodyExprPreFacts reasonEndpointResourcesPtr typedMemoryCopy slotCopyExecution
  gasOutcomeFullCompose gasOutcomeFullGuarded gasOutcomeFull gasContext gasExemptCert gasExplicitSites
  vyperStorageFootprint vyperStorageTrace vyperTypeInvariants vyperInterpreter vyperState
  vyperStorageBackend vyperTypeValues vyperTyping vyperAST vyperValue
  supportedStmts compileEnv stmtLowering context freshWrites exprLoweringProps
  emitHelper emitHelperProps fragExec fragGasOriginPtr ptrDiscipline
  venomState venomInst venomExecSemantics words finite_map list arithmetic
  vyperTypeContract[qualified,ignore_grammar]
Libs monadsyntax

Theorem for_captured_storage_continue_full:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt c lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body))
    sha = ((),shb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  c.ce_alloca_locals /\ local_ptrs_reserved c sa /\
  ret_pc_ok c sa s0 /\ return_buf_frame d c sa s0 /\ return_buf_sep d c em u /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_no_wrap inst t) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\ expr_body_pre c cx env e es /\
  expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
     (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
     for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
       (vv,se) H (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) em Gu tu u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     storage_well_formed_on cx es (FST H)) /\
  alloca_frame c es sa s0 c em u /\
  loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
  ~(?ty nid. e = TopLevelName ty nid) /\
  (!vs. (!tail. array_iterator_results cx (expr_type e)
                  (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) (em with gas_obs := tail) =
                  (INL vs,em with gas_obs := tail)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
    body_for_full_ok cx tyv id loop_body vs /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (array_iterator_results cx (expr_type e) (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))))
      (\items. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH items)) "For too long")
                         (eval_for cx tyv id loop_body items)))
    (em,u,Gu,tu) (for_array_loop_post (DF,lo,d,ctx,func) c cx lctx (es,sa,s0,G0,tn0) sb)
    (for_array_loop_exit ctx cx RetQ)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`sty` |-> `typ`, `fty` |-> `typ`] for_nonslot_array_layout_full_with_done_age) >>
  disch_then (qx_choosel_then [`vv0`,`se0`,`she`,`loc`,`lvo`,`sd`,`bc`,`saD`,`saA`,`p`,`nb`,`aidItem`,
     `entry`,`cond`,`bod`,`incr`,`exit`,`idx`,`invalid`,`valid`,`dv`,`next_var`,`shead`,
     `stride`,`off_op`,`sMul`,`sum_op`,`sAdd`,`addr`,`saCopy`,`sbCopy`,
     `sbBody`,`sj`,`shadow_sbCopy`,`shadow_sbBody`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [for_nonslot_layout_def]) >>
  `vv0 = vv /\ se0 = se` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `vv0 = vv` SUBST_ALL_TAC >> qpat_x_assum `se0 = se` SUBST_ALL_TAC >>
  qabbrev_tac `H0 = storage_trace_horizon em.storage_trace` >>
  `valid_horizon cx st0 H0 em.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS o
       REWRITE_RULE [for_array_expr_endpoint_def]))) >>
  qabbrev_tac `start = es with gas_obs := obs` >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e start = (INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))),em)` by
    (qpat_assum `em with gas_obs := [] = em` (fn eq =>
       qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `[]` mp_tac) >>
       simp[NoAsms,Abbr `start`,eq])) >>
  `expr_body_pre c cx env e start` by simp[Abbr `start`] >>
  suspend "capture"
QED

Resume for_captured_storage_continue_full[capture]:
  `!H. valid_horizon cx st0 H em.storage_trace ==>
    vv_post H ctx func c cx e start sa se s0 em (PlaceR (StoragePlace tr slot (ArrayTV tyv bd))) vv u /\
    storage_well_formed_on cx start (FST H) /\ storage_well_formed_on cx em (FST H) /\
    stmt_state_rel H ctx func c cx em u /\ ghost_inv_at (DF H) lo d c cx em Gu tu u` by
    suspend "horizon" >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ start _ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  drule_at_then (Pat `vv_post _ _ _ _ _ _ start _ _ _ _ _ _ _`) drule_all for_storage_iterator_operand >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?p. vv = LocatedValue _ _ /\ _` strip_assume_tac >>
  `loc = slot_loc tr` by fs[vv_location_def] >>
  qabbrev_tac `bop = vv_operand vv` >>
  `!x. bop = Var x ==> not_fresh_at se x` by
    (simp[NoAsms, Abbr `bop`] >> drule_all_then (ACCEPT_TAC o REWRITE_RULE [copy_old_operand_def])
       reasonEndpointResourcesPtrTheory.compile_expr_old_operand) >>
  drule_all for_captured_storage_code >> simp[NoAsms,LET_THM] >>
  qpat_assum `Abbrev (bop = _)` (fn th =>
    disch_then (map_every assume_tac o CONJUNCTS o
      REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  qpat_x_assum `?ov tot ep cb bb. _` strip_assume_tac >>
  suspend "initial"
QED

Resume for_captured_storage_continue_full[horizon]:
  gen_tac >> disch_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H start.storage_trace` suffices_by simp[Abbr `start`] >>
     irule (Q.ISPEC `eval_expr cx e` (Q.GEN `f` valid_horizon_frame)) >>
     qexistsl [`e`,`INL (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))`,`em`] >>
     simp[cj 5 evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H em.storage_trace ==> for_array_expr_endpoint _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS o
       REWRITE_RULE [for_array_expr_endpoint_def]))) >>
  qpat_assum `vv_post H _ _ _ _ _ es _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_def]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[Abbr `start`,vv_post_initial_gas] >>
  conj_tac >-
    (`storage_well_formed_on cx es (FST H)` by simp[] >>
     `storage_well_formed_on cx (es with gas_obs := obs) (FST H) =
      storage_well_formed_on cx es (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >>
     simp[Abbr `start`]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume for_captured_storage_continue_full[initial]:
  drule_then strip_assume_tac type_stmt_for_projection >>
  drule_all_then (assume_tac o CONJUNCT1) exprSimSourceTheory.expr_body_pre_eval_result >>
  `lookup_scopes id em.scopes = NONE` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`expr_sim_inv c cx env em`, `id NOTIN FDOM env.var_types`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `lookup_scopes id em.scopes` >>
     simp[expr_sim_inv_def,env_consistent_def,env_scopes_consistent_def,FLOOKUP_DEF] >> metis_tac[]) >>
  `stride = type_slot_size tyv /\ type_memory_bytes c typ = 32 * type_slot_size tyv` by
    (qpat_assum `stride = elem_size_in_location c (slot_loc tr) typ` SUBST1_TAC >>
     simp[slot_loc_def,NoAsms] >>
     conj_tac >- (irule (cj 1 for_storage_element_layout) >> qexistsl [`cx`,`env`,`em`] >>
                   rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule (cj 2 for_storage_element_layout) >> qexistsl [`cx`,`env`,`em`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `bound_length bd < dimword (:256)` by
    (qpat_assum `evaluate_type _ (expr_type e) = SOME _` mp_tac >>
     qpat_assum `expr_type e = ArrayT typ bd` (rewrite_tac o single) >>
     MATCH_ACCEPT_TAC typed_copy_array_count_bound) >>
  `type_memory_bytes c typ < 2 ** 64` by
    (qhdtm_assum `stmt_exprs_ok` mp_tac >> simp[NoAsms,stmt_exprs_ok_def,Once allocLimitsTheory.alloc_limits_stmt_def]) >>
  `nb < dimword (:256) /\ 32 * type_slot_size tyv <= nb` by
    (reverse conj_tac >- simp[] >> irule LESS_TRANS >> qexists `2 ** 64` >>
     conj_tac >- (qpat_assum `nb = type_memory_bytes c typ` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     simp[dimword_def,NoAsms]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (qpat_assum `return_buf_frame d c sa s0` (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     Cases_on `d` >> simp[return_buf_frame_def,pairTheory.FORALL_PROD,pairTheory.EXISTS_PROD] >>
     PairCases_on `x` >> rw[return_buf_frame_def] >> gvs[]) >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  qpat_assum `vv_post H0 _ _ _ _ _ start _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [vv_post_def]) >>
  `alloca_frame c start sa s0 c em u /\ ghost_kept_at lo c start sa G0 tn0 s0 Gu tu` by
    (conj_tac >- simp[Abbr `start`] >>
     qpat_assum `ghost_kept_at lo c es sa G0 tn0 s0 Gu tu` (mp_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     simp[NoAsms,Abbr `start`,ghost_kept_at_def] >>
     strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `bop = vv_operand vv` by simp[Abbr `bop`] >>
  drule_all for_captured_storage_initial_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`vs`,`len`,`dst`,`z`,`G`,`tn`] (map_every assume_tac o CONJUNCTS))) >>
  suspend "source"
QED

Resume for_captured_storage_continue_full[source]:
  qabbrev_tac `items = array_iterator_results cx (expr_type e)
    (PlaceR (StoragePlace tr slot (ArrayTV tyv bd)))` >>
  `items em = (INL vs,em)` by
    (qpat_assum `eval_iterator cx (Array e) start = _` mp_tac >>
     simp[NoAsms,Once evaluate_def,bind_def] >>
     qpat_assum `eval_expr cx e start = _` (fn th => simp[NoAsms,th,Abbr `items`])) >>
  `!tail. items (em with gas_obs := tail) = (INL vs,em with gas_obs := tail)` by
    (qpat_assum `items em = _` mp_tac >>
     Cases_on `bd` >> Cases_on `tr` >>
     simp[NoAsms,Abbr `items`,array_iterator_results_storage,result_array_length_def,
          get_storage_backend_eq,get_storage_def,bind_def,ignore_bind_def,
          check_def,assert_def,return_def,AllCaseEqs()]) >>
  `check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" = return ()` by
    (qpat_assum `len = LENGTH vs` (rewrite_tac o single o SYM) >>
     `len <= n` by decide_tac >> simp[FUN_EQ_THM,compatible_bound_def,check_def,assert_def,return_def]) >>
  `body_for_full_ok cx tyv id loop_body vs /\
   gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em` by
    (qpat_assum `!vs. _ ==> body_for_full_ok _ _ _ _ vs /\ _` irule >>
     simp[return_def] >> qpat_assum `!tail. items _ = _` (mp_tac o REWRITE_RULE [Abbr `items`]) >> simp[]) >>
  suspend "rounds"
QED

Resume for_captured_storage_continue_full[rounds]:
  cheat
QED

Finalise for_captured_storage_continue_full
