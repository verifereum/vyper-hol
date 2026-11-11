(*
 * A target rooted at a local ends on a live place: the path its evaluation
 * returns reads a value out of the local's current value, not only out of
 * its popped history.
 *
 * Each index bt[e] of the target runs after its base bt.  Either bt passes
 * through a dynamic-array element, and then the overlap rejection
 * (~target_subscript_overlap, targetOverlapAccess) says e writes no part of
 * bt's root, so by the local access frame (vyperLocalAccessFrame) the
 * local's scope entry is as it was; or bt's path crosses only fixed-size
 * arrays and structs (fixed_shape_path), which every well-typed value of
 * the local's type can read.
 *
 * TOP-LEVEL:
 *   local_base_place_live       — eval_base_place ends on a live place
 *   local_target_live           — eval_target_place ends on a live place
 *   local_subscript_index_live  — bt[e]'s base stays live after any
 *                                 successful run of e
 *)

Theory targetLocalLive
Ancestors
  vyperFixedShapePath allocLimits stmtSimAssignAttr targetOverlapAccess
  targetPlaceSim
  targetPlaceSimCasesBase
  targetSubscriptMemory exprSimSource exprSimHypsDefs
  vyperSubscriptOverlap vyperLocalAccessFrame
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants vyperTypeStatePreservation
  vyperPlaceStatePreservation vyperPlaceResultTyping vyperPlaceFrames
  vyperPlaceTyping vyperTyping vyperValue vyperValueOperation vyperMisc vyperAST
  vyperInterpreter vyperState list alist

(* ===== Typing of a local-rooted target ===== *)

Theorem local_target_type_only[local]:
  !bt env id vt.
    target_root bt = NameTarget id /\
    type_place_target env bt = SOME vt ==> ?ty. vt = Type ty
Proof
  Induct using base_assignment_target_induct >>
  simp[target_root_def, well_typed_expr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `ty` >> gvs[subscript_vtype_def] >>
  Cases_on `is_int_type (expr_type e)` >> gvs[]
QED

(* A local-rooted target's typing agrees with the lowering's place type. *)
Theorem local_target_place_type[local]:
  !bt cenv cx env s id bvt.
    expr_sim_inv cenv cx env s /\ target_root bt = NameTarget id /\
    type_place_target env bt = SOME bvt ==>
    ?ty. bvt = Type ty /\ target_place_type cenv bt = SOME (ValPT ty)
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- (rpt gen_tac >>
      simp[target_root_def, Once well_typed_expr_def, target_place_type_def,
           AllCaseEqs()] >>
      rpt strip_tac >> gvs[expr_sim_inv_def] >> metis_tac[])
  >- simp[target_root_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[target_root_def, Once well_typed_expr_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
  >- (Cases_on `ty` >> gvs[subscript_vtype_def] >>
      simp[target_place_type_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  Cases_on `tgt_ty` >> gvs[attribute_type_def] >>
  `attribute_type (get_tenv cx) (StructT p) s = SOME ty` by
    simp[attribute_type_def] >>
  drule_all stmtSimAssignAttrTheory.attribute_type_struct_field >>
  strip_tac >> simp[target_place_type_def]
QED

(* The local keeps its type across states meeting expr_sim_inv. *)
Theorem local_entry_type_kept[local]:
  expr_sim_inv cenv cx env a /\ expr_sim_inv cenv cx env b /\
  lookup_scopes id a.scopes = SOME ea ==>
  ?eb. lookup_scopes id b.scopes = SOME eb /\ eb.type = ea.type
Proof
  rpt strip_tac >>
  `env_scopes_consistent env cx a /\ env_scopes_consistent env cx b` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  qpat_x_assum `expr_sim_inv _ _ _ a` kall_tac >>
  qpat_x_assum `expr_sim_inv _ _ _ b` kall_tac >>
  fs[env_scopes_consistent_def] >>
  `IS_SOME (FLOOKUP env.var_types id)` by metis_tac[] >>
  Cases_on `FLOOKUP env.var_types id` >> gvs[] >>
  `IS_SOME (lookup_scopes id b.scopes)` by metis_tac[] >>
  Cases_on `lookup_scopes id b.scopes` >> gvs[] >>
  qpat_x_assum `!i ty en. _ /\ lookup_scopes i a.scopes = SOME en ==> _`
    (qspecl_then [`id`, `x`, `ea`] mp_tac) >>
  qpat_x_assum `!i ty en. _ /\ lookup_scopes i b.scopes = SOME en ==> _`
    (qspecl_then [`id`, `x`, `x'`] mp_tac) >> simp[]
QED

Theorem fixed_extension_step[local]:
  state_well_typed st /\ lookup_scopes id st.scopes = SOME entry /\
  fixed_shape_path entry.type path /\
  subscripts_type entry.type path = SOME tv /\
  extend_place cx (PlaceR (MemoryPlace id path)) sb st =
    (INL (PlaceR (MemoryPlace id out)),st) ==>
  out = path ++ [sb] /\ ?et. subscript_type tv sb = SOME et
Proof
  rpt strip_tac >>
  `value_has_type entry.type entry.value /\
   well_formed_type_value entry.type` by
    (irule scope_well_typed_lookup_scopes >>
     qexistsl [`id`, `st.scopes`] >> fs[state_well_typed_def]) >>
  `?v. evaluate_subscripts entry.type entry.value path = INL v` by
    metis_tac[fixed_shape_path_live] >>
  `value_has_type tv v` by metis_tac[evaluate_subscripts_type] >>
  `well_formed_type_value tv` by metis_tac[subscripts_type_well_formed] >>
  drule_all extend_place_memory_live_result >>
  disch_then (qspecl_then [`sb`, `cx`] mp_tac) >>
  Cases_on `evaluate_subscripts tv v [sb]` >> gvs[] >>
  `?et. subscripts_type tv [sb] = SOME et` by
    metis_tac[evaluate_subscripts_declared_type_exists] >>
  gvs[subscripts_type_def, AllCaseEqs()]
QED

(* A base that passes through no dynamic-array element ends on a fixed
   path, typed as the target. *)
Theorem local_base_fixed_shape[local]:
  !bt cenv cx env s ty id path s' entry.
  target_pre cenv cx env bt s /\
  type_place_target env bt = SOME (Type ty) /\
  target_root bt = NameTarget id /\
  eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),s') /\
  lookup_scopes id s'.scopes = SOME entry /\
  ~target_through_dynarray cenv bt ==>
  fixed_shape_path entry.type path /\
  ?tv. evaluate_type env.type_defs ty = SOME tv /\
       subscripts_type entry.type path = SOME tv
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- (rpt gen_tac >>
      simp[target_root_def, Once well_typed_expr_def, Once evaluate_def,
           bind_def, ignore_bind_def, get_scopes_def, type_check_def,
           assert_def, check_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      fs[target_pre_def, expr_sim_inv_def, env_consistent_def,
         env_context_consistent_def, env_scopes_consistent_def,
         subscripts_type_def, fixed_shape_path_def] >>
      qpat_x_assum `!i ty en. _ /\ lookup_scopes i s.scopes = SOME en ==> _`
        drule_all >> simp[])
  >- simp[target_root_def]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `target_pre cenv cx env bt s` by metis_tac[target_pre_sub] >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def] >>
      Cases_on `eval_base_place cx bt s` >> rename1 `(br,bs)` >>
      `expr_sim_inv cenv cx env bs` by metis_tac[eval_base_place_sim_inv] >>
      Cases_on `br` >> simp[] >>
      rename1 `eval_base_place cx bt s = (INL pv0,bs)` >>
      `expr_body_pre cenv cx env e bs` by
        fs[target_pre_def, target_indices_pre_def] >>
      Cases_on `eval_expr cx e bs` >> rename1 `(er,ms)` >>
      `expr_sim_inv cenv cx env ms` by
        metis_tac[exprSimSourceTheory.expr_body_pre_eval_result] >>
      Cases_on `er` >> simp[] >>
      rename1 `eval_expr cx e bs = (INL index,ms)` >>
      Cases_on `read_result cx index ms` >> rename1 `(rr,rs)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `rr` >> simp[] >> strip_tac >>
      drule extend_place_memory_origin >> strip_tac >>
      gvs[] >> imp_res_tac extend_place_state >> gvs[] >>
      `target_root bt = NameTarget id /\ ~target_through_dynarray cenv bt` by
        fs[target_root_def, target_through_dynarray_def] >>
      `?bvt. type_place_target env bt = SOME bvt` by
        fs[Once well_typed_expr_def, AllCaseEqs()] >>
      `expr_sim_inv cenv cx env s` by fs[target_pre_def] >>
      drule_all local_target_place_type >> strip_tac >> gvs[] >>
      rename1 `type_place_target env bt = SOME (Type bty)` >>
      `?oldentry. lookup_scopes id bs.scopes = SOME oldentry /\
                  oldentry.type = entry.type` by
        metis_tac[local_entry_type_kept] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      `state_well_typed ms` by fs[expr_sim_inv_def] >>
      drule_all fixed_extension_step >> strip_tac >> gvs[] >>
      gvs[Once well_typed_expr_def, subscript_vtype_def, AllCaseEqs()] >>
      Cases_on `bty` >> gvs[subscript_vtype_def] >>
      gvs[target_through_dynarray_def] >>
      Cases_on `b` >> gvs[] >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      drule subscript_type_value_int_shape >> strip_tac >> gvs[] >>
      gvs[subscript_type_def] >>
      simp[fixed_shape_path_append,
           vyperPlaceStatePreservationTheory.subscripts_type_append,
           fixed_shape_path_def, subscripts_type_def, subscript_type_def,
           vyperASTTheory.bound_length_def]) >>
  qx_gen_tac `bt` >> qx_gen_tac `attr` >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `target_pre cenv cx env bt s` by metis_tac[target_pre_sub] >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt s` >> rename1 `(br,bs)` >>
  `expr_sim_inv cenv cx env bs` by metis_tac[eval_base_place_sim_inv] >>
  Cases_on `br` >> simp[] >> strip_tac >>
  drule extend_place_memory_origin >> strip_tac >>
  gvs[] >> imp_res_tac extend_place_state >> gvs[] >>
  `target_root bt = NameTarget id /\ ~target_through_dynarray cenv bt` by
    fs[target_root_def, target_through_dynarray_def] >>
  `?bvt. type_place_target env bt = SOME bvt` by
    fs[Once well_typed_expr_def, AllCaseEqs()] >>
  drule_all local_target_type_only >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `state_well_typed bs` by fs[expr_sim_inv_def] >>
  drule_all fixed_extension_step >> strip_tac >> gvs[] >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >>
  drule_all attribute_type_runtime_step >> strip_tac >>
  Cases_on `ty'` >> gvs[attribute_type_def] >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  simp[fixed_shape_path_append,
       vyperPlaceStatePreservationTheory.subscripts_type_append,
       fixed_shape_path_def, subscripts_type_def]
QED

(* ===== Liveness across an index ===== *)

(* An index of a target whose base passes through a dynamic-array element
   leaves the base's root local as it was. *)
Theorem dynarray_index_keeps_local[local]:
  target_pre cenv cx env (SubscriptTarget bt e) s /\
  target_root bt = NameTarget id /\ target_through_dynarray cenv bt /\
  bind (eval_expr cx e) (read_result cx) a = (INL key,b) ==>
  lookup_scopes id b.scopes = lookup_scopes id a.scopes
Proof
  rpt strip_tac >>
  `~target_subscript_overlap cenv bt e` by
    fs[target_pre_def, target_indices_pre_def] >>
  `~MEM (WriteAcc (LocalRef id)) (expr_accesses cenv.ce_modules e)` by
    metis_tac[target_subscript_overlap_unwritten,
              target_root_local_nonconstant_read] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  irule eval_expr_unwritten_local >>
  gvs[expr_accesses_def] >> metis_tac[]
QED

(* A live base place stays live across any successful run of the index. *)
Theorem index_keeps_live[local]:
  target_pre cenv cx env (SubscriptTarget bt e) s /\
  type_place_target env bt = SOME bvt /\ target_root bt = NameTarget id /\
  eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),mid) /\
  lookup_scopes id mid.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
    (INL key,fin) ==>
  ?entry' v'. lookup_scopes id fin.scopes = SOME entry' /\
    evaluate_subscripts entry'.type entry'.value path = INL v'
Proof
  rpt strip_tac >>
  `target_pre cenv cx env bt s` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env mid` by metis_tac[eval_base_place_sim_inv] >>
  Cases_on `target_through_dynarray cenv bt`
  >- (`lookup_scopes id fin.scopes = SOME entry` by
        (drule_all dynarray_index_keeps_local >> simp[]) >>
      metis_tac[]) >>
  drule_all local_target_type_only >> strip_tac >> gvs[] >>
  drule_all local_base_fixed_shape >> strip_tac >>
  `expr_body_pre cenv cx env e (mid with gas_obs := gs)` by
    fs[target_pre_def, target_indices_pre_def] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def] >>
  Cases_on `eval_expr cx e (mid with gas_obs := gs)` >> rename1 `(er,st)` >>
  `expr_sim_inv cenv cx env st` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval_result] >>
  Cases_on `er` >> simp[] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  drule_all local_entry_type_kept >> strip_tac >>
  `value_has_type eb.type eb.value /\ well_formed_type_value eb.type` by
    (irule scope_well_typed_lookup_scopes >>
     qexistsl [`id`, `fin.scopes`] >>
     fs[expr_sim_inv_def, state_well_typed_def]) >>
  metis_tac[fixed_shape_path_live]
QED

(* ===== The exported forms ===== *)

Theorem local_base_place_live:
  !bt cenv cx env s id vt pv t.
    target_pre cenv cx env bt s /\ type_place_target env bt = SOME vt /\
    target_root bt = NameTarget id /\ eval_base_place cx bt s = (INL pv,t) ==>
    ?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id t.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac
  >- (rpt gen_tac >>
      simp[target_root_def, Once evaluate_def, bind_def, ignore_bind_def,
           get_scopes_def, type_check_def, assert_def, check_def,
           return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `lookup_scopes id t.scopes` >>
      gvs[evaluate_subscripts_def, optionTheory.IS_SOME_EXISTS])
  >- simp[target_root_def]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `target_pre cenv cx env bt s` by metis_tac[target_pre_sub] >>
      `target_root bt = NameTarget id` by fs[target_root_def] >>
      `?basevt. type_place_target env bt = SOME basevt` by
        fs[Once well_typed_expr_def, AllCaseEqs()] >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def] >>
      Cases_on `eval_base_place cx bt s` >> rename1 `(br,bs)` >>
      Cases_on `br` >> simp[] >>
      rename1 `eval_base_place cx bt s = (INL basepv,bs)` >>
      `?path entry v. basepv = PlaceR (MemoryPlace id path) /\
        lookup_scopes id bs.scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL v` by
        (first_x_assum drule_all >> simp[]) >> gvs[] >>
      Cases_on `eval_expr cx e bs` >> rename1 `(er,ms)` >>
      Cases_on `er` >> simp[] >>
      Cases_on `read_result cx x ms` >> rename1 `(rr,rs)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `rr` >> simp[] >> strip_tac >>
      `bind (eval_expr cx e) (read_result cx) (bs with gas_obs := bs.gas_obs) =
        (INL x',ms)` by simp[bind_def] >>
      drule_all index_keeps_live >> strip_tac >>
      drule_all extend_place_memory_live >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  qx_gen_tac `bt` >> qx_gen_tac `attr` >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `target_pre cenv cx env bt s` by metis_tac[target_pre_sub] >>
  `target_root bt = NameTarget id` by fs[target_root_def] >>
  `?basevt. type_place_target env bt = SOME basevt` by
    fs[Once well_typed_expr_def, AllCaseEqs()] >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt s` >> rename1 `(br,bs)` >>
  Cases_on `br` >> simp[] >> strip_tac >>
  `?path entry v. x = PlaceR (MemoryPlace id path) /\
    lookup_scopes id bs.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v` by
    (first_x_assum drule_all >> simp[]) >> gvs[] >>
  drule_all extend_place_memory_live >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem local_target_live:
  !cenv cx env s bt vt id path t entry.
    target_pre cenv cx env bt s /\ type_place_target env bt = SOME vt /\
    target_root bt = NameTarget id /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?live. evaluate_subscripts entry.type entry.value path = INL live
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all local_base_place_live >> strip_tac >>
  gvs[get_place_def, return_def, raise_def]
QED

Theorem local_subscript_index_live:
  !cenv cx env s bt e bvt id pv mid gs key fin.
    target_pre cenv cx env (SubscriptTarget bt e) s /\
    type_place_target env bt = SOME bvt /\ target_root bt = NameTarget id /\
    eval_base_place cx bt s = (INL pv,mid) /\
    bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
      (INL key,fin) ==>
    ?path entry v. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id fin.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt strip_tac >>
  `target_pre cenv cx env bt s` by metis_tac[target_pre_sub] >>
  drule_all local_base_place_live >> strip_tac >> gvs[] >>
  drule_all index_keeps_live >> strip_tac >> metis_tac[]
QED
