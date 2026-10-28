(* TOP-LEVEL: abi_target_operand_pop_sound — source-derived target validity.
   Helpers: root shape, projection/path typing, and capture observation frames.
   No cell-read readiness hypotheses are introduced. *)
Theory vyperTypeAbiTargetSoundness
Ancestors
  list rich_list arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperTyping vyperTypeSystem
  vyperState vyperContext vyperMisc vyperAbiReadTyping vyperAbiStateTyping
  vyperTypeExprSoundness vyperAbiOperand vyperAbiExprTyping
  vyperAbiProjectionTyping vyperAbiReadOnly
  vyperAbiFrame vyperCallOutcomeFrame vyperTypeInvariants vyperTypeEnv vyperTypeValues
Libs
  monadsyntax

val abi_target_operand_observations =
  let
    val frame = Q.INST [`R` |-> `λs t:evaluation_state.
      t.scopes = s.scopes /\ t.immutables = s.immutables /\
      t.accounts = s.accounts`] state_rel_frame_abi_primitives
    val premise = fst (dest_imp (concl frame))
    val valid = prove (premise, simp[] >> metis_tac[])
    val frames = MATCH_MP frame valid |>
      SIMP_RULE (srw_ss()) [state_rel_frame_result]
    val SOME result = List.find
      (fn th => can (find_term (same_const ``abi_target_operand``)) (concl th))
      (CONJUNCTS frames)
  in save_thm ("abi_target_operand_observations", result) end;

Theorem base_target_runtime_typed_observations:
  rt.scopes = st.scopes /\ rt.immutables = st.immutables ==>
  (target_runtime_typed env cx rt (BaseTarget bt) ty (BaseTargetV loc subs) <=>
   target_runtime_typed env cx st (BaseTarget bt) ty (BaseTargetV loc subs))
Proof
  strip_tac >> Cases_on `loc` >>
  simp[target_runtime_typed_def, location_runtime_typed_def,
       get_immutables_def, get_address_immutables_def, lift_option_type_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[return_def, raise_def]
QED

Theorem base_target_value_shape_nonbare:
  !bt src id subs.
  base_target_value_shape env bt (TopLevelVar src id) subs ==>
  FLOOKUP env.bare_globals (src,id) = NONE
Proof
  Induct >> simp[base_target_value_shape_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem pop_immutable_target_projected:
  well_typed_expr env (Pop elem_ty bt) /\
  target_runtime_typed env cx st (BaseTarget bt) ty
    (BaseTargetV (ImmutableVar src id) subs) ==>
  subs <> []
Proof
  Cases_on `bt` >>
  simp[Once well_typed_expr_def, target_runtime_typed_def,
       target_value_shape_def, base_target_value_shape_def, target_mutable_def,
       location_runtime_typed_def] >> rpt strip_tac >> gvs[]
QED

Theorem target_path_type_complex_root:
  !subs env vt final.
    target_path_type env vt subs final /\
    (subs <> [] \/ ?ty bd. final = Type (ArrayT ty bd)) ==>
    (?ty bd. vt = Type (ArrayT ty bd)) \/
    (?sid. vt = Type (StructT sid)) \/ (?kt rest. vt = HashMapT kt rest)
Proof
  Induct >> simp[target_path_type_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `subs`
  >- (gvs[target_path_type_def] >>
      rename1 `target_path_step_type env root_vt first_sub final` >>
      Cases_on `root_vt` >> simp[] >>
      rename1 `target_path_step_type env (Type root_ty) first_step final` >>
      Cases_on `root_ty` >> gvs[target_path_step_type_def, AllCaseEqs()]) >>
  first_x_assum irule >> simp[] >> goal_assum drule
QED

Theorem target_path_type_array_root_nonprimitive:
  target_path_type env (Type root_ty) subs (Type (ArrayT ty bd)) /\
  evaluate_type env.type_defs root_ty = SOME tv ==>
  ~abi_primitive tv
Proof
  strip_tac >> drule target_path_type_complex_root >> simp[] >> strip_tac >>
  gvs[Once evaluate_type_def, abi_primitive_def, AllCaseEqs()]
QED

Theorem abi_target_step_shape:
  target_path_step_type env (Type root_ty) sub vt /\
  evaluate_type env.type_defs root_ty = SOME parent ==>
  ?ty tv. vt = Type ty /\ evaluate_type env.type_defs ty = SOME tv /\
          abi_projection_shape parent sub tv
Proof
  Cases_on `root_ty` >>
  simp[target_path_step_type_def, AllCaseEqs()] >> rpt strip_tac
  >- (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      (Cases_on `sub` >| [
        rename1 `ValueSubscript sub_value` >> Cases_on `sub_value` >>
          gvs[abi_projection_shape_def],
        gvs[abi_projection_shape_def]])) >>
  Cases_on `sub` >> gvs[AllCaseEqs()] >>
  `?fields. parent = StructTV fields` by
    (Cases_on `parent` >> gvs[Once evaluate_type_def, AllCaseEqs()]) >>
  gvs[] >> drule_all attribute_type_evaluates >> strip_tac >>
  gvs[abi_projection_shape_def]
QED

Theorem project_abi_path_append:
  !left arg. project_abi_path cx arg (left ++ right) =
    do middle <- project_abi_path cx arg left;
       project_abi_path cx middle right od
Proof
  Induct >> simp[project_abi_path_def, FUN_EQ_THM, bind_def, return_def] >>
  rpt gen_tac >>
  qmatch_goalsub_rename_tac `project_abi_operand cx argument first_sub initial_st` >>
  Cases_on `project_abi_operand cx argument first_sub initial_st` >>
  rename1 `project_abi_operand cx argument first_sub initial_st = (step_res,step_st)` >>
  Cases_on `step_res` >> simp[]
QED

Theorem project_abi_operand_not_snapshot:
  project_abi_operand cx arg sub st = (INL out,rt) ==>
  ~?v. out = AbiSnapshot v
Proof
  Cases_on `arg` >> Cases_on `sub` >>
  simp[project_abi_operand_def, ignore_bind_def, bind_def, UNCURRY, AllCaseEqs(),
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), ignore_bind_def, bind_def, UNCURRY, return_def, raise_def] >>
  qmatch_asmsub_rename_tac `value_type_CASE child_vt` >> Cases_on `child_vt` >>
  gvs[AllCaseEqs(), bind_def, return_def, raise_def]
QED

Theorem abi_target_step_valid:
  env.type_defs = get_tenv cx /\
  well_formed_vtype env.type_defs vt /\
  abi_place_result_valid env st arg vt /\ (~?v. arg = AbiSnapshot v) /\
  target_path_step_type env vt sub vt' /\
  project_abi_operand cx arg sub st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL out => well_formed_vtype env.type_defs vt' /\
       abi_place_result_valid env rt out vt' /\ (~?v. out = AbiSnapshot v)
   | INR _ => T
Proof
  strip_tac >> Cases_on `vt`
  >- (qpat_x_assum `env.type_defs = get_tenv cx` kall_tac >>
      gvs[abi_place_result_valid_def] >>
      drule_all abi_target_step_shape >> strip_tac >> gvs[] >>
      imp_res_tac evaluate_type_well_formed_type_value >>
      drule_all (SRULE [] abi_projection_valid) >> strip_tac >>
      Cases_on `res` >> gvs[] >>
      simp[well_formed_vtype_def, well_formed_type_def,
           abi_place_result_valid_def] >>
      drule project_abi_operand_not_snapshot >> simp[] >>
      goal_assum drule >> simp[]) >>
  rename1 `well_formed_vtype env.type_defs (HashMapT key_ty result_vt)` >>
  gvs[abi_place_result_valid_def, target_path_step_type_def, AllCaseEqs()] >>
  Cases_on `result_vt` >> Cases_on `sub` >>
  gvs[well_formed_vtype_def, well_formed_type_def, IS_SOME_EXISTS,
      project_abi_operand_def, lift_option_type_def, bind_def,
      return_def, abi_place_result_valid_def, abi_operand_valid_def,
      no_type_error_result_def] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem abi_target_path_valid:
  !subs env arg vt vt' cx st res rt.
  env.type_defs = get_tenv cx /\
  well_formed_vtype env.type_defs vt /\
  abi_place_result_valid env st arg vt /\ (~?v. arg = AbiSnapshot v) /\
  target_path_type env vt subs vt' /\
  project_abi_path cx arg (REVERSE subs) st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL out => well_formed_vtype env.type_defs vt' /\
       abi_place_result_valid env rt out vt' /\ (~?v. out = AbiSnapshot v)
   | INR _ => T
Proof
  Induct
  >- (simp[target_path_type_def, project_abi_path_def, return_def,
           no_type_error_result_def] >> rpt gen_tac >> strip_tac >> gvs[]) >>
  simp[target_path_type_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `project_abi_path _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[REVERSE_DEF, project_abi_path_append, bind_def] >>
  Cases_on `project_abi_path cx arg (REVERSE subs) st` >>
  rename1 `project_abi_path cx arg (REVERSE subs) st = (path_res,path_st)` >>
  first_x_assum (drule_all o SRULE []) >> strip_tac >> gvs[] >>
  Cases_on `path_res` >> gvs[]
  >- (simp[project_abi_path_def, bind_def, return_def] >> strip_tac >>
      qmatch_asmsub_rename_tac `project_abi_operand cx middle last_sub projection_st` >>
      Cases_on `project_abi_operand cx middle last_sub projection_st` >>
      rename1 `project_abi_operand cx middle last_sub projection_st = (step_res,step_st)` >>
      Cases_on `step_res` >> gvs[] >>
      qpat_assum `env.type_defs = get_tenv cx`
        (fn eq => drule_all (SRULE [eq] (SPEC_ALL abi_target_step_valid))) >>
      simp[]) >>
  strip_tac >> gvs[]
QED

Theorem abi_target_array_path_valid:
  env.type_defs = get_tenv cx /\
  well_formed_vtype env.type_defs vt /\
  abi_place_result_valid env st arg vt /\ (~?v. arg = AbiSnapshot v) /\
  target_path_type env vt subs (Type (ArrayT elem_ty (Dynamic n))) /\
  project_abi_path cx arg (REVERSE subs) st = (res,rt) ==>
  no_type_error_result res /\
  case res of INL out => ?tv.
    evaluate_type env.type_defs elem_ty = SOME tv /\
    abi_operand_valid rt (ArrayTV tv (Dynamic n)) out /\
    (~?v. out = AbiSnapshot v)
   | INR _ => T
Proof
  strip_tac >> drule_all abi_target_path_valid >> strip_tac >>
  Cases_on `res` >>
  gvs[abi_place_result_valid_def, Once evaluate_type_def, AllCaseEqs()]
QED

(* ===== Source-derived target roots ===== *)

Theorem abi_scoped_target_pop_valid[local]:
  runtime_consistent env cx st /\
  location_runtime_typed env cx st (ScopedVar id) (Type root_ty) /\
  target_path_type env (Type root_ty) subs (Type (ArrayT elem_ty (Dynamic n))) /\
  abi_target_operand cx (ScopedVar id) subs st = (res,rt) ==>
  no_type_error_result res /\
  case res of INL out => ?tv.
    evaluate_type env.type_defs elem_ty = SOME tv /\
    abi_operand_valid rt (ArrayTV tv (Dynamic n)) out /\ (~?v. out = AbiSnapshot v)
   | INR _ => T
Proof
  strip_tac >> gvs[location_runtime_typed_def] >>
  rename1 `lookup_scopes id st.scopes = SOME entry` >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (irule scope_well_typed_lookup_scopes >>
     fs[runtime_consistent_def, state_well_typed_def] >> goal_assum drule >> simp[]) >>
  `~abi_primitive entry.type` by
    (drule_all target_path_type_array_root_nonprimitive >> simp[]) >>
  `?captured. capture_abi_memory cx id entry.type entry.value st =
      (INL (LENGTH st.abi_memory),captured) /\
      abi_operand_valid captured entry.type
        (AbiMemory (LENGTH st.abi_memory) 0 entry.type)` by
    (irule capture_abi_memory_valid >> simp[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `abi_target_operand _ _ _ _ = _` mp_tac >>
  asm_simp_tac(srw_ss())[abi_target_operand_def, lookup_abi_local_def, get_scopes_def,
    lift_option_type_def, bind_def, return_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  `well_formed_vtype env.type_defs (Type root_ty)` by
    simp[well_formed_vtype_def, well_formed_type_def] >>
  `abi_place_result_valid env captured
      (AbiMemory (LENGTH st.abi_memory) 0 entry.type) (Type root_ty)` by
    (simp[abi_place_result_valid_def] >> goal_assum drule >> simp[]) >>
  `~?v. AbiMemory (LENGTH st.abi_memory) 0 entry.type = AbiSnapshot v` by simp[] >>
  drule_all abi_target_array_path_valid >> simp[]
QED

Theorem abi_immutable_target_pop_valid[local]:
  runtime_consistent env cx st /\
  location_runtime_typed env cx st (ImmutableVar src id) (Type root_ty) /\
  target_path_type env (Type root_ty) subs (Type (ArrayT elem_ty (Dynamic n))) /\
  subs <> [] /\
  abi_target_operand cx (ImmutableVar src id) subs st = (res,rt) ==>
  no_type_error_result res /\
  case res of INL out => ?tv.
    evaluate_type env.type_defs elem_ty = SOME tv /\
    abi_operand_valid rt (ArrayTV tv (Dynamic n)) out /\ (~?v. out = AbiSnapshot v)
   | INR _ => T
Proof
  strip_tac >> gvs[location_runtime_typed_def] >>
  rename1 `get_immutables cx src st = (INL imms,st)` >>
  rename1 `FLOOKUP imms id = SOME (tv,v)` >>
  `value_has_type tv v /\ well_formed_type_value tv` by
    (`imms = get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m)` by
       (qpat_x_assum `get_immutables cx src st = _` mp_tac >>
        rw[get_immutables_def, get_address_immutables_def, bind_def, return_def,
           lift_option_type_def, lift_option_def, raise_def] >>
        Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]) >>
     gvs[] >>
     `imms_well_typed (case ALOOKUP st.immutables cx.txn.target of
        NONE => [] | SOME m => m)` by
       (irule current_immutables_well_typed >> fs[runtime_consistent_def]) >>
     drule_all imms_well_typed_get_source_immutables >> simp[]) >>
  `~abi_primitive tv` by
    (drule_all target_path_type_array_root_nonprimitive >> simp[]) >>
  `?captured. capture_abi_immutable cx src id tv v st =
      (INL (LENGTH st.abi_immutables),captured) /\
      abi_operand_valid captured tv (AbiImmutable (LENGTH st.abi_immutables) 0 tv)` by
    (irule capture_abi_immutable_valid >> simp[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `abi_target_operand _ _ _ _ = _` mp_tac >>
  Cases_on `subs` >> fs[] >>
  rename1 `target_path_type env (Type root_ty) (first_sub::remaining_subs)
    (Type (ArrayT elem_ty (Dynamic n)))` >>
  asm_simp_tac(srw_ss())[abi_target_operand_def, lookup_abi_immutable_def,
    lift_option_type_def, bind_def, return_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  `well_formed_vtype env.type_defs (Type root_ty)` by
    simp[well_formed_vtype_def, well_formed_type_def] >>
  `abi_place_result_valid env captured
      (AbiImmutable (LENGTH st.abi_immutables) 0 tv) (Type root_ty)` by
    (simp[abi_place_result_valid_def] >> goal_assum drule >> simp[]) >>
  `~?v. AbiImmutable (LENGTH st.abi_immutables) 0 tv = AbiSnapshot v` by simp[] >>
  `project_abi_path cx (AbiImmutable (LENGTH st.abi_immutables) 0 tv)
      (REVERSE (first_sub::remaining_subs)) captured = (res,rt)` by simp[REVERSE_DEF] >>
  drule_all abi_target_array_path_valid >> simp[]
QED

Theorem abi_global_target_pop_valid[local]:
  runtime_consistent env cx st /\
  location_runtime_typed env cx st (TopLevelVar src id) vt /\
  FLOOKUP env.bare_globals (src,id) = NONE /\
  target_path_type env vt subs (Type (ArrayT elem_ty (Dynamic n))) /\
  abi_target_operand cx (TopLevelVar src id) subs st = (res,rt) ==>
  no_type_error_result res /\
  case res of INL out => ?tv.
    evaluate_type env.type_defs elem_ty = SOME tv /\
    abi_operand_valid rt (ArrayTV tv (Dynamic n)) out /\ (~?v. out = AbiSnapshot v)
   | INR _ => T
Proof
  strip_tac >>
  `env_consistent env cx st` by fs[runtime_consistent_def] >>
  `well_formed_vtype env.type_defs vt` by
    (fs[location_runtime_typed_def, runtime_consistent_def,
        env_consistent_def, env_context_consistent_def] >>
     first_x_assum drule >> simp[]) >>
  gvs[location_runtime_typed_def] >> Cases_on `vt`
  >- (rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type root_ty)` >>
      drule_all env_consistent_toplevel_storage_static >> strip_tac >>
      gvs[IS_SOME_EXISTS, abi_target_operand_def, lookup_abi_global_def,
          bind_def, lift_option_type_def, return_def] >>
      rename1 `project_abi_path cx (AbiStorage tr slot root_tv) (REVERSE subs) st = (res,rt)` >>
      `env.type_defs = get_tenv cx` by
        fs[env_consistent_def, env_context_consistent_def] >>
      `well_formed_type_value root_tv` by
        metis_tac[evaluate_type_well_formed_type_value] >>
      `abi_place_result_valid env st (AbiStorage tr slot root_tv) (Type root_ty)` by
        simp[abi_place_result_valid_def, abi_operand_valid_def] >>
      `~?v. AbiStorage tr slot root_tv = AbiSnapshot v` by simp[] >>
      drule_all abi_target_array_path_valid >> simp[]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[IS_SOME_EXISTS, abi_target_operand_def, lookup_abi_global_def,
      bind_def, lift_option_type_def, return_def] >>
  rename1 `project_abi_path cx (AbiMapping tr slot key_ty rest_vt) (REVERSE subs) st = (res,rt)` >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `abi_place_result_valid env st (AbiMapping tr slot key_ty rest_vt)
      (HashMapT key_ty rest_vt)` by simp[abi_place_result_valid_def] >>
  `~?v. AbiMapping tr slot key_ty rest_vt = AbiSnapshot v` by simp[] >>
  drule_all abi_target_array_path_valid >> simp[]
QED

(* Public consumer boundary: constructor projections remain genuine immutable
   pointers, while only the direct immutable root is excluded by Pop typing. *)
Theorem abi_target_operand_pop_sound:
  runtime_consistent env cx st /\ well_typed_expr env (Pop elem_ty bt) /\
  target_runtime_typed env cx st (BaseTarget bt)
    (ArrayT elem_ty (Dynamic n)) (BaseTargetV loc subs) /\
  abi_target_operand cx loc subs st = (res,rt) ==>
  runtime_consistent env cx rt /\ no_type_error_result res /\
  target_runtime_typed env cx rt (BaseTarget bt)
    (ArrayT elem_ty (Dynamic n)) (BaseTargetV loc subs) /\
  case res of INL out => ?tv.
    evaluate_type env.type_defs elem_ty = SOME tv /\
    abi_operand_valid rt (ArrayTV tv (Dynamic n)) out /\ (~?v. out = AbiSnapshot v)
   | INR _ => T
Proof
  strip_tac >> drule abi_target_operand_observations >> strip_tac >>
  drule_all abi_typing_observations_frame >> strip_tac >>
  drule_all base_target_runtime_typed_observations >> strip_tac >>
  `runtime_consistent env cx rt` by fs[runtime_consistent_def] >>
  `?vt. location_runtime_typed env cx st loc vt /\
        target_path_type env vt subs (Type (ArrayT elem_ty (Dynamic n)))` by
    (fs[target_runtime_typed_def] >> goal_assum drule >> simp[]) >>
  pop_assum strip_assume_tac >>
  rename1 `location_runtime_typed env cx st loc root_vt` >>
  Cases_on `loc`
  >- (Cases_on `root_vt`
      >- (drule_all abi_scoped_target_pop_valid >> simp[]) >>
      gvs[location_runtime_typed_def])
  >- (`subs <> []` by (drule_all pop_immutable_target_projected >> simp[]) >>
      Cases_on `root_vt`
      >- (drule_all abi_immutable_target_pop_valid >> simp[]) >>
      gvs[location_runtime_typed_def]) >>
  rename1 `location_runtime_typed env cx st (TopLevelVar src id) root_vt` >>
  `base_target_value_shape env bt (TopLevelVar src id) subs` by
    fs[target_runtime_typed_def, target_value_shape_def] >>
  drule_all base_target_value_shape_nonbare >> strip_tac >>
  drule_all abi_global_target_pop_valid >> simp[]
QED
