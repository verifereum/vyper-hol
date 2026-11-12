(*
 * pop_expr_ptr_ok's cases by the target's root, for bodyPtrPop, as S1's
 * exprSimPopNested.pop_nested_sim splits them:
 *   - a top-level name: bodyPtrPopRootCase's body_pop_root_ptr_ok (in
 *     bodyPtrPop itself);
 *   - a bare local: the seam bodyPtrPopSeamLocalRoot;
 *   - a nested target rooted at a module name with no storage
 *     declaration (an immutable or a constant): at runtime such a target
 *     does not type, as in S1's pop_nested_immutable_runtime_sim;
 *   - a nested target rooted at a storage or transient variable: with
 *     pure indices, the seam bodyPtrPopSeamStoragePure over the target's
 *     fragment; otherwise the held residual
 *     bodyPtrPopResidualStorageEffectful;
 *   - a nested target rooted at a local: with local_target_live, the seam
 *     bodyPtrPopSeamNestedLocalLive over the target's fragment; otherwise
 *     the held residual bodyPtrPopResidualNestedLocalPopped.
 * The target's fragment (pop_target_frag_ptr) is the seams
 * bodyPtrPopSeamTargetSim and bodyPtrPopSeamTargetFrag.
 *
 * TOP-LEVEL:
 *   pop_vv_ptr_cases
 *)
Theory bodyPtrPopCompose
Ancestors
  bodyPtrPopSeamLocalRoot bodyPtrPopSeamStoragePure bodyPtrPopSeamTargetSim
  bodyPtrPopSeamTargetFrag bodyPtrPopSeamNestedLocalLive
  bodyPtrPopResidualStorageEffectful bodyPtrPopResidualNestedLocalPopped
  bodyPtrPopTargetDefs popTargetPre bodyPtrPreds bodyPtrDefs bodySim
  exprSimHypsDefs targetPlaceSim targetPlaceLive vyperTypeEnv
  vyperTypeInvariants vyperTypeSystem vyperPureExpr vyperInterpreter
  vyperState vyperAST

Theorem pop_target_root_cases[local]:
  !bt. (?id. target_root bt = NameTarget id) \/
       (?src id. target_root bt = TopLevelNameTarget (src,id))
Proof
  `(!e:expr. T) /\
   !bt. (?id. target_root bt = NameTarget id) \/
        (?src id. target_root bt = TopLevelNameTarget (src,id))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  rw[target_root_def] >> Cases_on `p` >> simp[]
QED

(* As exprSimPopNested's no_storage_root_untyped_runtime. *)
Theorem no_storage_root_untyped_runtime[local]:
  !env cx src id.
    env_context_consistent env cx /\ ~cx.in_deploy /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    type_place_target env (TopLevelNameTarget (src,id)) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >> simp[] >>
  gvs[type_place_target_TopLevelNameTarget,
      env_context_consistent_def, bare_global_assignable_complete_def] >>
  Cases_on `x` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  res_tac >> gvs[]
QED

(* As exprSimPopNested's target_root_untyped. *)
Theorem target_root_untyped[local]:
  !env bt. type_place_target env (target_root bt) = NONE ==>
    type_place_target env bt = NONE
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> simp[target_root_def] >> rpt strip_tac >>
  first_x_assum (drule_at Any) >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `type_place_target env tgt` >>
  Cases_on `type_place_target env tgt` >> simp[] >>
  gvs[Abbr `tgt`, type_place_target_AttributeTarget,
      type_place_target_SubscriptTarget]
QED

(* A target rooted at a module name with no storage declaration (an
   immutable or a constant): the runtime judgment's ~cenv.ce_is_ctor and
   body_inv give ~cx.in_deploy, where bare_global_assignable is empty, so
   the root, hence the pop, does not type (S1's
   pop_nested_immutable_runtime_sim). *)
Theorem pop_nested_immutable_vv_ptr[local]:
  !tops ctx cenv cx env ann bt ty es d PG func src id.
    body_inv tops ctx cenv cx /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_sim_ptr_def] >>
  rpt strip_tac >>
  `~cx.in_deploy` by gvs[body_inv_def] >>
  `env_context_consistent env cx` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def] >>
  `type_place_target env (target_root bt) = NONE` by
    metis_tac[no_storage_root_untyped_runtime] >>
  drule target_root_untyped >> strip_tac >>
  `well_typed_expr env (Pop ann bt)` by metis_tac[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr env (Pop ann bt)` mp_tac >>
  simp[Once well_typed_expr_def]
QED

(* The target's fragment, for a target rooted at a live local or at a
   storage variable through pure indices. *)
Theorem pop_nested_frag_ptr[local]:
  !tops ctx cenv cx env ann bt es d PG func.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx bt /\
    expr_body_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt /\
    (!id. target_root bt = NameTarget id ==> local_target_live cx id bt) /\
    (!src id. target_root bt = TopLevelNameTarget (src,id) ==>
              EVERY pure_expr (target_indices bt)) ==>
    pop_target_frag_ptr d ctx PG func cenv cx env bt es
Proof
  rpt strip_tac >> irule pop_target_frag_ptr_of_sim >>
  irule body_target_sim_ptr >> simp[] >>
  metis_tac[target_pre_of_pop]
QED

(* A nested target rooted at a local: live, or a residual. *)
Theorem pop_nested_local_root_vv_ptr[local]:
  !tops ctx cenv cx env ann bt ty es d PG func id.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx bt /\
    (!x. bt <> NameTarget x) /\ target_root bt = NameTarget id /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `local_target_live cx id bt`
  >- (`~immutable_root cx bt` by fs[immutable_root_def] >>
      `pop_target_frag_ptr d ctx PG func cenv cx env bt es` by
        (irule pop_nested_frag_ptr >> fs[] >> metis_tac[]) >>
      metis_tac[pop_nested_local_live_vv_ptr]) >>
  irule pop_nested_local_popped_case_ptr >> simp[] >> metis_tac[]
QED

(* A nested target rooted at a storage or transient variable: pure
   indices, or a residual. *)
Theorem pop_nested_storage_vv_ptr[local]:
  !tops ctx cenv cx env ann bt ty es d PG func src id ts vd.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx bt /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME vd /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `EVERY pure_expr (target_indices bt)`
  >- (`~immutable_root cx bt` by fs[immutable_root_def] >>
      `pop_target_frag_ptr d ctx PG func cenv cx env bt es` by
        (irule pop_nested_frag_ptr >> fs[] >> metis_tac[]) >>
      metis_tac[pop_nested_storage_pure_vv_ptr]) >>
  irule pop_nested_storage_effectful_dead_case_ptr >> metis_tac[]
QED

(* Every target but a top-level name, by its root. *)
Theorem pop_vv_ptr_cases:
  !tops ctx cenv cx env ann bt ty es d PG func.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx bt /\
    (!nid. bt <> TopLevelNameTarget nid) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `?id. bt = NameTarget id`
  >- (gvs[] >> metis_tac[pop_local_root_vv_ptr]) >>
  `!x. bt <> NameTarget x` by metis_tac[] >>
  qspec_then `bt` strip_assume_tac pop_target_root_cases
  >- metis_tac[pop_nested_local_root_vv_ptr] >>
  Cases_on `?ts vd. get_module_code cx src = SOME ts /\
                    find_var_decl_by_name id ts = SOME vd`
  >- (gvs[] >> metis_tac[pop_nested_storage_vv_ptr]) >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts = NONE` by
    (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >> metis_tac[]) >>
  metis_tac[pop_nested_immutable_vv_ptr]
QED
