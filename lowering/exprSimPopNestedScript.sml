(*
 * Expression simulation: pop on a nested target (x.a.pop(), x[i].pop(),
 * self.s.a.pop(), self.m[k].pop()).
 *
 * The lowering takes the array's pointer, location and type from
 * compile_get_target_ptr, as an assignment does, then runs
 * compile_dynarray_pop at that pointer.  The case lemmas take the target's
 * fragment judgment (pop_target_frag, which targetPlaceSimCases'
 * target_place_sim gives from target_sim) and split on the target's root.
 * pop_target_frag, the helpers and pop_nested_storage_pure_sim are in
 * exprSimPopNestedBase; each other lemma is in its own theory, named
 * after it (exprSimPopNestedStorageEffectful, exprSimPopNestedImmutableDeploy,
 * exprSimPopNestedLocal, exprSimPopNestedTargetFrag,
 * bodyPopNestedTargetFrag):
 *
 *   pop_nested_storage_pure_sim — a storage or transient root with pure
 *                             indices: the header load and store and the
 *                             element's slots, as exprSimPopStorage's
 *                             compile_pop_storage_sim has them at a
 *                             declared variable's slot.
 *   pop_nested_storage_effectful_sim — RESIDUAL: a storage root with an
 *                             index that pops or calls, which can leave
 *                             the target's header dead.
 *   pop_nested_immutable_runtime_sim — an immutable or constant root at
 *                             runtime: such a target does not type
 *                             (bare_global_assignable is empty at runtime).
 *   pop_nested_immutable_deploy_sim — RESIDUAL: an immutable root in the
 *                             constructor, which Python accepts for a
 *                             member of a complex immutable.
 *   pop_nested_local_sim    — RESIDUAL: a memory local root, whose
 *                             nested length word locals_kept does not
 *                             exempt yet.
 *
 *   pop_nested_expr_target_frag — the target's fragment judgment at the
 *                             expression level.
 *)

Theory exprSimPopNested
Ancestors
  exprSimPopNestedBase exprSimPopNestedStorageEffectful
  exprSimPopNestedImmutableDeploy exprSimPopNestedLocal
  exprSimPopNestedTargetFrag bodyPopNestedTargetFrag
  loweringPosts bodySim exprSimHypsDefs
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

Theorem pop_nested_storage_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `EVERY pure_expr (target_indices bt)`
  >- (irule pop_nested_storage_pure_sim >> metis_tac[]) >>
  irule pop_nested_storage_effectful_sim >> metis_tac[]
QED

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

(* An immutable or constant root at runtime: bare_global_assignable is
   empty outside the constructor (bare_global_assignable_complete), so the
   root names a bare global, which type_place_target rejects, and the pop
   does not type. *)
Theorem pop_nested_immutable_runtime_sim:
  !ctx func cenv cx env ann bt ty es src id.
    ~cx.in_deploy /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `env_context_consistent env cx` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def] >>
  `type_place_target env (target_root bt) = NONE` by
    metis_tac[no_storage_root_untyped_runtime] >>
  drule target_root_untyped >> strip_tac >>
  `well_typed_expr env (Pop ann bt)` by metis_tac[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr env (Pop ann bt)` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Theorem no_module_root_untyped[local]:
  !env cx src id.
    env_context_consistent env cx /\ get_module_code cx src = NONE ==>
    type_place_target env (TopLevelNameTarget (src,id)) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >> simp[] >>
  gvs[type_place_target_TopLevelNameTarget, env_context_consistent_def] >>
  TRY (Cases_on `x`) >> gvs[] >> res_tac >> gvs[]
QED

(* A root in no module: the root does not type, so neither does the pop. *)
Theorem pop_nested_no_module_sim[local]:
  !ctx func cenv cx env ann bt ty es src id.
    get_module_code cx src = NONE /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `env_context_consistent env cx` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def] >>
  `type_place_target env (target_root bt) = NONE` by
    metis_tac[no_module_root_untyped] >>
  drule target_root_untyped >> strip_tac >>
  `well_typed_expr env (Pop ann bt)` by metis_tac[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr env (Pop ann bt)` mp_tac >>
  simp[Once well_typed_expr_def]
QED

(* In the constructor, a nested pop's immutable root is assignable (its
   target types, and a bare global that is not assignable has a storage
   declaration), so expr_sim_inv's bare_globals_layout gives
   pop_nested_sim's constructor premises: the compile env is the
   constructor's exactly when the context is in deploy, and the root's
   declared type is in ce_module_var_type. *)
Theorem pop_nested_immutable_root_ctor:
  !cenv cx env es ann bt src id.
    expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt) /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    (cenv.ce_is_ctor <=> cx.in_deploy) /\
    !ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
          cenv.ce_module_var_type (src,id) = SOME ty0
Proof
  rpt gen_tac >> strip_tac >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  `bare_globals_layout cenv.ce_is_ctor cenv.ce_module_var_type
     cenv.ce_module_vars cx env.bare_globals env.bare_global_assignable` by
    fs[expr_sim_inv_def] >>
  `!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
         FLOOKUP env.bare_globals (src,id) = SOME ty0` by
    (fs[env_context_consistent_def] >> metis_tac[]) >>
  `?ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty` by
    (drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
     Cases_on `type_place_target env (TopLevelNameTarget (src,id))`
     >- (qspecl_then [`env`, `bt`] mp_tac target_root_untyped >> simp[]) >>
     gvs[type_place_target_TopLevelNameTarget] >>
     rename1 `FLOOKUP env.toplevel_vtypes _ = SOME vt` >> Cases_on `vt` >>
     fs[env_context_consistent_def] >> res_tac >> gvs[]) >>
  fs[bare_globals_layout_def] >> metis_tac[]
QED

Theorem target_root_cases[local]:
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

(* By the target's root: a local, a storage or transient variable, or a
   module name with no storage declaration (an immutable or a constant). *)
Theorem pop_nested_sim:
  !ctx func cenv cx env ann bt ty es.
    (~immutable_root cx bt ==> pop_target_frag ctx func cenv cx env bt es) /\
    (immutable_root cx bt ==>
     ?nocalls. target_idx_case nocalls ctx func cenv cx bt /\
               (nocalls ==> int_calls_target bt = [])) /\
    (immutable_root cx bt /\ cx.in_deploy ==>
     cenv.ce_is_ctor /\
     !src id ty0. target_root bt = TopLevelNameTarget (src,id) /\
                  FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
                  cenv.ce_module_var_type (src,id) = SOME ty0) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >>
  qspec_then `bt` strip_assume_tac target_root_cases
  >- (`~immutable_root cx bt` by gvs[immutable_root_def] >>
      irule pop_nested_local_sim >> metis_tac[]) >>
  Cases_on `?ts d. get_module_code cx src = SOME ts /\
                   find_var_decl_by_name id ts = SOME d`
  >- (gvs[] >> `~immutable_root cx bt` by gvs[immutable_root_def] >>
      irule pop_nested_storage_sim >> metis_tac[]) >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts = NONE` by
    (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >> metis_tac[]) >>
  Cases_on `cx.in_deploy`
  >- (Cases_on `get_module_code cx src`
      >- (irule pop_nested_no_module_sim >> metis_tac[]) >>
      `immutable_root cx bt` by (simp[immutable_root_def] >> metis_tac[]) >>
      gvs[] >> irule pop_nested_immutable_deploy_sim >>
      rpt conj_tac
      >- gvs[] >- gvs[] >- (qexistsl [`env`,`id`,`src`] >> gvs[]) >>
      metis_tac[]) >>
  irule pop_nested_immutable_runtime_sim >> metis_tac[]
QED
