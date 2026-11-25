(*
 * The for statement of the full body induction (bodySimFullMain), over
 * the finite-horizon joint judgment: the iterator's joint fragment, then
 * the loop's rounds (stmtSimForRounds' H-indexed invariant), each body
 * run a joint fragment, sharing one origin/memory/pointer witness.
 *
 * TOP-LEVEL:
 *   compile_for_frag_full -- body_for_case_full's fragment
 *)
Theory bodyFullFor
Ancestors
  bodyFullShadowBodyInv
  bodyFullForControl bodyFullForRounds stateRelProj haltExitProj
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST list
  bodyFullForFrame bodyFullForHandlers bodyFullForRange bodyFullForStorageRoute
  bodyFullForArrayBranch bodyFullForIteratorRoot bodyFullForIteratorHeld
  bodyStorageMetadata vyperSubscriptOverlap vyperValue vyperTyping
  vyperTypeContract[qualified,ignore_grammar]

val _ = Parse.hide "body";

Theorem compile_for_frag_full:
  !cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (For id typ it n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    stmt_loop_calls_ok [(NONE,tops)] (For id typ it n body) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es
Proof
  rpt gen_tac >> strip_tac >> Cases_on `it`
  >- suspend "array"
  >- suspend "range"
QED

Resume compile_for_frag_full[range]:
  rename1 `For id typ (Range a b) n body` >>
  qspecl_then
    [`cx`,`id`,`typ`,`a`,`b`,`n`,`body`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,
     `ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
     `lctx`,`RetQ`,`es`] (MATCH_MP_TAC)
    bodyFullForRangeTheory.compile_for_range_frag_full >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC for_full_frame_compose) >>
  conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC for_full_frame_pop) >>
  conj_tac >- ACCEPT_TAC for_body_cleanup_full >>
  conj_tac >- (simp[] >> MATCH_ACCEPT_TAC (SRULE [] for_full_exit_scopes_gas_obs)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_for_frag_full[array]:
  rename1 `For id typ (Array e) n body` >>
  Cases_on `?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
                     supported_storage_value tops nid (ArrayT typ bd)`
  >- (pop_assum strip_assume_tac >>
      qpat_assum `e = TopLevelName (ArrayT typ bd) nid` SUBST_ALL_TAC >>
      qspecl_then
        [`cx`,`id`,`typ`,`bd`,`nid`,`n`,`body`,`DF`,`lo`,`d`,`PG`,`tops`,
         `bindings`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,
         `ret_ty`,`lctx`,`RetQ`,`es`] MATCH_MP_TAC
        bodyFullForStorageRouteTheory.compile_for_storage_array_frag_full >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL stmtSimDefsTheory.alloca_frame_trans)) >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL bodySimFullTheory.alloca_taint_kept_trans)) >>
      conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SPEC_ALL bodyFullForControlTheory.halt_exit_scopes_gas_obs)) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all bodySimTheory.body_inv_stmt_const_name_free >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          supportedStmtTraverseTheory.supported_iterator_exists_def]) >>
  Cases_on `~(?ty nid. e = TopLevelName ty nid) /\
      (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid)`
  >- (pop_assum strip_assume_tac >> suspend "nested_array") >>
  `~(?ty nid. e = TopLevelName ty nid) ==>
    !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid` by
    metis_tac[] >>
  qspecl_then
    [`cx`,`id`,`typ`,`e`,`n`,`body`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,
     `ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,
     `lctx`,`RetQ`,`es`] MATCH_MP_TAC
    bodyFullForArrayBranchTheory.compile_for_nonslot_array_frag_full >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_for_frag_full[nested_array]:
  `well_typed_expr env e` by
    fs[Once type_stmt_def, well_typed_iterator_def, AllCaseEqs()] >>
  `supported_expr tops e` by
    (drule_then strip_assume_tac bodyFullForFactsTheory.supported_stmt_for_projection >>
     Cases_on `e` >> gvs[supportedStmtsTheory.supported_iterator_def,
                           vyperTypeContractTheory.loop_iterator_place_def,
                           targetPlaceSimTheory.target_root_def]) >>
  drule_all_then strip_assume_tac bodyFullForIteratorRootTheory.supported_nested_iterator_root_kind
  >- (qspecl_then
        [`cx`,`id`,`typ`,`e`,`n`,`body`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,
         `ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`]
        MATCH_MP_TAC bodyFullForIteratorHeldTheory.compile_for_immutable_subplace_array_frag_full >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexistsl [`tgt`,`nid`] >> simp[]) >>
  qspecl_then
    [`cx`,`id`,`typ`,`e`,`n`,`body`,`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,
     `ctx`,`shadow_ctx`,`func`,`shadow_func`,`cenv`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`]
    MATCH_MP_TAC bodyFullForIteratorHeldTheory.compile_for_storage_subplace_array_frag_full >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`tgt`,`nid`] >> simp[] >> metis_tac[]
QED

Finalise compile_for_frag_full
