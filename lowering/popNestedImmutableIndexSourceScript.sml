(* Source readability of an immutable target across its actual index run. *)
Theory popNestedImmutableIndexSource
Ancestors
  popNestedImmutableIndexFrame popNestedImmutableTransport
  popNestedImmutablePathMemory popNestedImmutableFrame popNestedImmutableAccess
  popNestedImmutableTypeMemory targetOverlapAccess bodySim bodySimEntry
  exprSimProps exprSimHypsDefs exprSimSource exprSimPopImmutableTarget
  exprSimWordArgs loweringPosts gasSummary
  loweringShapeProps supportedNames supportedProgram
  vyperTypeInvariants vyperTypeCallStackSoundness vyperStatePreservation
  vyperImmutableMetadataFrame vyperSubscriptOverlap vyperState vyperInterpreter
  vyperMisc targetPlaceSim targetPlaceSimCasesBase list alist finite_map

Theorem find_function_unique_member[local]:
  !tops vis mut nr raw name args dflts ret body.
    ALL_DISTINCT (supported_function_names tops) /\
    MEM (FunctionDecl vis mut nr raw name args dflts ret body) tops ==>
    find_function name tops = SOME (dflts,body)
Proof
  Induct >- simp[find_function_def] >>
  Cases_on `h` >> rw[find_function_def, supported_function_names_def] >>
  gvs[] >> metis_tac[MEM_supported_function_names]
QED

Theorem imm_place_at_readable_root[local]:
  imm_place_at cenv cx mid (PlaceR (ImmutablePlace src id path)) w ty /\
  get_immutables cx src mid = (INL imms,mid) /\
  FLOOKUP imms id = SOME (root,a) /\
  get_immutables cx src fin = (INL imms',fin) /\
  FLOOKUP imms' id = SOME (root,a') /\
  evaluate_subscripts root a' path = INL v ==>
  imm_place_at cenv cx fin (PlaceR (ImmutablePlace src id path)) w ty
Proof
  Cases_on `ALOOKUP mid.immutables cx.txn.target` >>
  Cases_on `ALOOKUP fin.immutables cx.txn.target` >>
  simp[imm_place_at_def, get_immutables_def, get_address_immutables_def,
    bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem body_immutable_callable_match[local]:
  body_inv tops ctx cenv cx ==>
  !src fn ts mut nr args dflts ret body.
    get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut,nr,args,dflts,ret,body) ==>
    ALOOKUP cenv.ce_modules src = SOME ts /\
    (find_function fn ts = SOME (dflts,body) \/ (dflts = [] /\ body = []))
Proof
  strip_tac >> drule body_inv_modules_aligned >> strip_tac >>
  rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
  `ts = tops /\ ALL_DISTINCT (supported_function_names tops)` by
    (fs[body_inv_def, supported_program_def, supported_declaration_names_def] >>
     qpat_x_assum `!src ts. get_module_code cx src = SOME ts ==> src = NONE`
       (qspecl_then [`src`, `ts`] mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  drule lookup_callable_function_SOME_decompose >> strip_tac >> simp[] >>
  disj1_tac >> irule find_function_unique_member >> metis_tac[]
QED

Theorem immutable_target_nonconstant[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env st /\
  FLOOKUP env.bare_globals (src,id) = SOME ty ==>
  !ts. ALOOKUP cenv.ce_modules src = SOME ts ==> ~constant_decl id ts
Proof
  strip_tac >>
  `env_context_consistent env cx` by fs[expr_sim_inv_def, env_consistent_def] >>
  drule_all env_context_consistent_bare_global_find_NONE >> strip_tac >>
  drule body_inv_modules_aligned >> strip_tac >>
  `ts = tops /\ src = NONE /\ supported_declaration_headers tops` by
    (fs[body_inv_def, supported_program_def] >>
     qpat_x_assum `!src ts. get_module_code cx src = SOME ts ==> src = NONE`
       (qspecl_then [`src`, `ts`] mp_tac) >> simp[] >> strip_tac >> gvs[]) >> gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    (qpat_assum `!src ts. get_module_code cx src = SOME ts ==> ALL_DISTINCT _`
       (qspecl_then [`NONE`, `tops`] irule) >> first_assum ACCEPT_TAC) >>
  drule_all supported_bare_global_immutable >> strip_tac >>
  drule_all immutable_decl_not_constant_decl >> metis_tac[]
QED

Theorem immutable_target_index_lookup[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env st /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  target_root bt = TopLevelNameTarget (src,id) /\
  target_through_dynarray cenv bt /\ ~target_subscript_overlap cenv bt e /\
  expr_body_pre cenv cx env e mid /\
  bind (eval_expr cx e) (read_result cx) mid = (res,fin) ==>
  FLOOKUP (case ALOOKUP fin.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
  FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables src imms) id
Proof
  strip_tac >>
  `!ts. ALOOKUP cenv.ce_modules src = SOME ts ==> ~constant_decl id ts` by
    metis_tac[immutable_target_nonconstant] >>
  drule_all target_root_state_nonconstant_read >> disch_tac >>
  drule_all target_subscript_overlap_unwritten >> strip_tac >>
  drule body_immutable_callable_match >> disch_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  (imp_res_tac read_result_state >> gvs[] >>
   drule_at (Pat `eval_expr _ _ _ = _`) (BETA_RULE eval_expr_unwritten_immutable) >>
   disch_then (qspecl_then [`env`, `cenv.ce_modules`, `src`, `id`] mp_tac) >>
   impl_tac >- (fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >> simp[])
QED

Theorem imm_place_at_index_source:
  body_inv tops ctx cenv cx /\ target_pre cenv cx env bt st /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL (PlaceR (ImmutablePlace src id path)),mid) /\
  ~target_subscript_overlap cenv bt e /\ expr_body_pre cenv cx env e mid /\
  bind (eval_expr cx e) (read_result cx) mid = (res,fin) ==>
  !w. imm_place_at cenv cx mid (PlaceR (ImmutablePlace src id path)) w ty ==>
    imm_place_at cenv cx fin (PlaceR (ImmutablePlace src id path)) w ty
Proof
  rpt strip_tac >> Cases_on `target_through_dynarray cenv bt`
  >- (`expr_sim_inv cenv cx env st` by fs[target_pre_def] >>
      drule_all pop_nested_immutable_root_bare >> strip_tac >>
      drule_all immutable_target_index_lookup >> disch_tac >>
      fs[imm_place_at_def] >> metis_tac[]) >>
  drule_all pop_nested_immutable_path_typed >> strip_tac >>
  drule pop_nested_immutable_path_fixed >> simp[] >> disch_tac >>
  drule pop_nested_immutable_static_index_ready >> simp[] >> strip_tac >>
  irule imm_place_at_readable_root >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem imm_target_post_gas_obs[simp]:
  (imm_target_post ctx func cenv cx (es with gas_obs := gs) sa sb s0 ee pv ty r t <=>
   imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t) /\
  (imm_target_post ctx func cenv cx es sa sb s0 (ee with gas_obs := gs) pv ty r t <=>
   imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t)
Proof
  simp[imm_target_post_def, oneline imm_place_at_def,
       locals_kept_def, popped_kept_def]
QED

Theorem imm_target_post_index_source:
  body_inv tops ctx cenv cx /\ target_pre cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt es = (INL pv,em) /\
  ~target_subscript_overlap cenv bt e /\ expr_body_pre cenv cx env e em /\
  bind (eval_expr cx e) (read_result cx) em = (res,ee) /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  imm_target_post ctx func cenv cx es sa sm s0 em pv ty rb t /\
  (!l. FST rb <> Label l) /\
  expr_post ctx func cenv cx e em sm sn t ee v op u ==>
  imm_target_post ctx func cenv cx es sa sn s0 ee pv ty rb u
Proof
  strip_tac >>
  `!w. imm_place_at cenv cx em pv w ty ==>
       imm_place_at cenv cx ee pv w ty` by
    (Cases_on `pv`
     >- simp[imm_place_at_def]
     >- (rename1 `PlaceR pp` >> Cases_on `pp`
         >- simp[imm_place_at_def]
         >- simp[imm_place_at_def] >>
         metis_tac[imm_place_at_index_source]) >>
     simp[imm_place_at_def]) >>
  metis_tac[imm_target_post_index]
QED

Theorem imm_target_post_index_marked_source:
  body_inv tops ctx cenv cx /\ target_pre cenv cx env bt es /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  ~target_subscript_overlap cenv bt e /\
  expr_body_pre cenv cx env e (mid with gas_obs := []) /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) left (INL pv) mid (OK t) /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (mid with gas_obs := [],t) marks (INL v) ee (OK u) /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  imm_target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := [])
    pv ty rb t /\ (!l. FST rb <> Label l) /\
  expr_post ctx func cenv cx e (mid with gas_obs := []) sm sn t
    (ee with gas_obs := []) v op u ==>
  imm_target_post ctx func cenv cx es sa sn s0 (ee with gas_obs := [])
    pv ty rb u
Proof
  strip_tac >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit left s0.vs_gas_readings ++
                          gas_explicit marks t.vs_gas_readings) =
     (INL pv, mid with gas_obs := gas_explicit marks t.vs_gas_readings)` by
    (fs[gas_marked_exec_def] >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (mid with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v, ee with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  `target_pre cenv cx env bt
     (es with gas_obs := gas_explicit left s0.vs_gas_readings ++
                          gas_explicit marks t.vs_gas_readings)` by
    fs[target_pre_def] >>
  `expr_body_pre cenv cx env e
     (mid with gas_obs := gas_explicit marks t.vs_gas_readings)` by fs[] >>
  `!w. imm_place_at cenv cx
          (mid with gas_obs := gas_explicit marks t.vs_gas_readings) pv w ty ==>
       imm_place_at cenv cx (ee with gas_obs := []) pv w ty` by
    (Cases_on `pv`
     >- simp[imm_place_at_def]
     >- (rename1 `PlaceR pp` >> Cases_on `pp`
         >- simp[imm_place_at_def]
         >- simp[imm_place_at_def] >>
         metis_tac[imm_place_at_index_source]) >>
     simp[imm_place_at_def]) >>
  `!w. imm_place_at cenv cx (mid with gas_obs := []) pv w ty ==>
       imm_place_at cenv cx (ee with gas_obs := []) pv w ty` by
    (qpat_x_assum `!w. imm_place_at _ _ _ _ _ _ ==> _` mp_tac >>
     simp[oneline imm_place_at_def]) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by simp[] >>
  metis_tac[imm_target_post_index]
QED
