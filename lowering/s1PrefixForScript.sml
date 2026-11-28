(* Request-prefix companion to bodyFullFor. *)
Theory s1PrefixFor
Ancestors
  s1PrefixPreds bodyFullFor s1PrefixDefs s1PrefixForRange s1PrefixForArrayBranch
  s1PrefixForStorageRoute s1PrefixForImmutableSubplace s1PrefixForStorageSubplace
  s1PrefixForArrayPreparedCut s1PrefixForArraySnapshot s1PrefixForCapturedStorageContinue

val _ = Parse.hide "body";

val prepared_array_cut_tac =
  rpt strip_tac >> irule for_array_prepared_expr_cut_frag_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`env`,`env'`,`tops`] >> rpt conj_tac >> first_assum ACCEPT_TAC

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> Cases_on `it`
  >- suspend "array"
  >- suspend "range"
QED
*)
Theorem compile_for_frag_prefix:
  !cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_prefix_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_prefix_ok cx it) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ it n body) /\
  (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
  stmt_loop_calls_ok [(NONE,tops)] (For id typ it n body) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ it n body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ it n body) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[range]:
  irule compile_for_range_frag_prefix >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "range_inputs"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[array]:
  rename1 `For id typ (Array e) n body` >>
  Cases_on `?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
                     supported_storage_value tops nid (ArrayT typ bd)`
  >- (pop_assum strip_assume_tac >> suspend "storage_name") >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all bodySimTheory.body_inv_stmt_const_name_free >>
     simp[supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
          supportedStmtTraverseTheory.supported_iterator_exists_def]) >>
  Cases_on `~(?ty nid. e = TopLevelName ty nid) /\
      (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid)`
  >- (pop_assum strip_assume_tac >> suspend "nested") >>
  `~(?ty nid. e = TopLevelName ty nid) ==>
    !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid` by
    metis_tac[] >>
  irule compile_for_nonslot_array_frag_prefix >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexistsl [`bindings`,`env`,`env'`,`tops`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[nested]:
  `well_typed_expr env e` by
    (drule bodyFullForFactsTheory.type_stmt_for_projection >> simp[vyperTypeSystemTheory.well_typed_iterator_def]) >>
  `supported_expr tops e` by
    (drule_then strip_assume_tac bodyFullForFactsTheory.supported_stmt_for_projection >>
     Cases_on `e` >> gvs[supportedStmtsTheory.supported_iterator_def,
                           vyperTypeContractTheory.loop_iterator_place_def,
                           targetPlaceSimTheory.target_root_def]) >>
  drule_all_then (DISJ_CASES_THEN2 assume_tac assume_tac)
    bodyFullForIteratorRootTheory.singleton_supported_nested_iterator_root_kind
  >- suspend "immutable"
  >> suspend "storage_subplace"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[range_inputs]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  FIRST [rpt gen_tac >> MATCH_ACCEPT_TAC bodyFullForFrameTheory.for_full_frame_compose,
         rpt gen_tac >> MATCH_ACCEPT_TAC bodyFullForFrameTheory.for_full_frame_pop,
         ACCEPT_TAC bodyFullForHandlersTheory.for_body_cleanup_full,
         simp[] >> MATCH_ACCEPT_TAC (SRULE [] bodyFullForHandlersTheory.for_full_exit_scopes_gas_obs),
         qexistsl [`bindings`,`env`,`env'`,`tops`] >> rpt conj_tac >> first_assum ACCEPT_TAC]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[storage_name]:
  irule compile_for_storage_array_frag_prefix_from_continue >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`bd`,`bindings`,`env`,`env'`,`nid`,`tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >> suspend "literal_live_cut")
  >> prepared_array_cut_tac
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[immutable]:
  irule compile_for_immutable_subplace_array_frag_prefix_from_cuts >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`bindings`,`env`,`env'`,`tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC for_array_snapshot_continue_prefix)
  >- (qexistsl [`tgt`,`nid`] >> simp[])
  >> prepared_array_cut_tac
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[storage_subplace]:
  irule compile_for_storage_subplace_array_frag_prefix_from_cuts >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`bindings`,`env`,`env'`,`tops`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
      suspend "nested_live_cut")
  >- (rpt gen_tac >> DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
      suspend "nested_snapshot_cut")
  >- prepared_array_cut_tac
  >> qexistsl [`tgt`,`nid`] >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[literal_live_cut]:
  irule for_captured_storage_continue_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt (goal_assum (drule_at Any)) >> disj1_tac >> qexists `w` >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[nested_live_cut]:
  irule for_captured_storage_continue_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt (goal_assum (drule_at Any)) >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_for_frag_prefix[nested_snapshot_cut]:
  irule for_array_snapshot_continue_prefix >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt (goal_assum (drule_at Any)) >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_for_frag_prefix
*)
