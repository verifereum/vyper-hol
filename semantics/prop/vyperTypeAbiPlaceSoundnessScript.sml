(* Bridge the source evaluator's captured places to delayed ABI operands. *)
Theory vyperTypeAbiPlaceSoundness
Ancestors
  list rich_list option pair arithmetic finite_map vyperAST vyperValue vyperState
  vyperInterpreter vyperAbiOperand vyperTyping vyperTypeSystem vyperTypeInvariants
  vyperTypeEnv vyperTypeValues vyperTypeExprSoundness vyperStatePreservation
  vyperTypeStatePreservation vyperPlaceStatePreservation
  vyperPlaceTyping vyperPlaceResultTyping vyperAbiExprTyping vyperAbiReadTyping
  vyperAbiProjectionTyping vyperAbiStateTyping vyperTypeGlobalLookupSoundness
  vyperAbiFrame vyperCallOutcomeFrame vyperPlaceWriteSoundness

Theorem abi_subscript_type_shape:
  subscript_type parent sub = SOME child ==> abi_projection_shape parent sub child
Proof
  Cases_on `parent` >> Cases_on `sub` >>
  TRY (rename1 `ValueSubscript index` >> Cases_on `index`) >>
  simp[subscript_type_def, abi_projection_shape_def, AllCaseEqs(), oEL_THM]
QED

Theorem project_abi_operand_not_snapshot:
  (~?v. arg = AbiSnapshot v) /\ project_abi_operand cx arg sub st = (INL out,rt) ==>
  ~?v. out = AbiSnapshot v
Proof
  Cases_on `arg` >> Cases_on `sub` >>
  simp[project_abi_operand_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, lift_option_type_def, PULL_EXISTS] >>
  rpt strip_tac >> gvs[UNCURRY, value_type_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      AllCaseEqs(), bind_def, lift_option_type_def, return_def, raise_def]
QED

Theorem project_abi_path_valid:
  !path parent child arg cx st res rt.
  abi_operand_valid st parent arg /\ (~?v. arg = AbiSnapshot v) /\
  subscripts_type parent path = SOME child /\
  project_abi_path cx arg path st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL out => abi_operand_valid rt child out /\ (~?v. out = AbiSnapshot v)
            | INR _ => T
Proof
  Induct >> simp[project_abi_path_def, subscripts_type_def, return_def,
                no_type_error_result_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  rename1 `subscript_type parent h = SOME step_tv` >>
  drule abi_subscript_type_shape >> strip_tac >>
  `well_formed_type_value parent` by (Cases_on `arg` >> fs[abi_operand_valid_def]) >>
  `well_formed_type_value step_tv` by
    (drule_all subscript_type_well_formed >> simp[]) >>
  Cases_on `project_abi_operand cx arg h st` >>
  rename1 `project_abi_operand cx arg h st = (head_res,head_st)` >>
  drule_all (SRULE [] abi_projection_valid) >> strip_tac >> gvs[] >>
  Cases_on `head_res` >> gvs[bind_def, no_type_error_result_def] >>
  drule_all (SRULE [] project_abi_operand_not_snapshot) >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem subscripts_array_not_primitive:
  !path root et bd.
    subscripts_type root path = SOME (ArrayTV et bd) ==> ~abi_primitive root
Proof
  Induct >> simp[subscripts_type_def] >> rpt gen_tac >> strip_tac
  >- gvs[abi_primitive_def] >>
  Cases_on `root` >> Cases_on `h` >>
  TRY (rename1 `ValueSubscript index` >> Cases_on `index`) >>
  gvs[subscripts_type_def, subscript_type_def, abi_primitive_def, AllCaseEqs()]
QED

Theorem lookup_abi_local_location:
  lookup_scopes id st.scopes = SOME entry /\
  well_formed_type_value entry.type /\ value_has_type entry.type entry.value /\
  ~abi_primitive entry.type ==>
  ?arg rt. lookup_abi_local cx id st = (INL arg,rt) /\
    abi_operand_valid rt entry.type arg /\ (~?v. arg = AbiSnapshot v) /\
    (state_well_typed rt <=> state_well_typed st) /\
    (!env. env_consistent env cx rt <=> env_consistent env cx st) /\
    rt.accounts = st.accounts
Proof
  strip_tac >>
  `?rt. capture_abi_memory cx id entry.type entry.value st = (INL (LENGTH st.abi_memory),rt) /\
        abi_operand_valid rt entry.type (AbiMemory (LENGTH st.abi_memory) 0 entry.type)` by
    (irule capture_abi_memory_valid >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule capture_abi_memory_typing_frame >> strip_tac >>
  simp[lookup_abi_local_def, bind_def, get_scopes_def, lift_option_type_def,
       return_def] >> goal_assum drule >> simp[]
QED

Theorem lookup_abi_memory_place_valid:
  lookup_scopes id st.scopes = SOME entry /\
  well_formed_type_value entry.type /\ value_has_type entry.type entry.value /\
  well_formed_type_value tv /\ subscripts_type entry.type path = SOME tv /\
  lookup_abi_memory_place cx id path st = (res,rt) ==>
  (state_well_typed rt <=> state_well_typed st) /\
  (!env. env_consistent env cx rt <=> env_consistent env cx st) /\
  rt.accounts = st.accounts /\ no_type_error_result res /\
  case res of INL arg => abi_operand_valid rt tv arg /\ (~?v. arg = AbiSnapshot v)
            | INR _ => T
Proof
  strip_tac >>
  `?writes. encode_value entry.type entry.value = SOME writes` by
    metis_tac[value_has_type_equiv, IS_SOME_EXISTS] >>
  drule subscripts_type_abi_offset >> strip_tac >>
  Cases_on `read_memory_path entry path` >>
  gvs[lookup_abi_memory_place_def, get_scopes_def, bind_def,
      lift_option_type_def, lift_sum_def, capture_abi_memory_at_def,
      return_def, raise_def, AllCaseEqs(), abi_operand_valid_def,
      no_type_error_result_def] >>
  drule_all read_memory_path_typed_error >> simp[]
QED

Theorem lookup_abi_immutable_location:
  get_immutables cx src st = (INL imms,st) /\
  FLOOKUP imms id = SOME (root,a) /\
  well_formed_type_value root /\ value_has_type root a /\ ~abi_primitive root ==>
  ?arg rt. lookup_abi_immutable cx src id st = (INL arg,rt) /\
    abi_operand_valid rt root arg /\ (~?v. arg = AbiSnapshot v) /\
    (state_well_typed rt <=> state_well_typed st) /\
    (!env. env_consistent env cx rt <=> env_consistent env cx st) /\
    rt.accounts = st.accounts
Proof
  strip_tac >>
  `?rt. capture_abi_immutable cx src id root a st = (INL (LENGTH st.abi_immutables),rt) /\
        abi_operand_valid rt root (AbiImmutable (LENGTH st.abi_immutables) 0 root)` by
    (irule capture_abi_immutable_valid >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule capture_abi_immutable_typing_frame >> strip_tac >>
  simp[lookup_abi_immutable_def, bind_def, lift_option_type_def, return_def] >>
  goal_assum drule >> simp[]
QED

Theorem extend_storage_place_not_immutable:
  extend_storage_place cx tr slot tv sub st = (INL (ImmutablePlace src id path),rt) ==> F
Proof
  Cases_on `tv` >> Cases_on `sub` >>
  TRY (rename1 `ValueSubscript index` >> Cases_on `index`) >>
  simp[extend_storage_place_def, UNCURRY, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()]
QED

Theorem extend_place_not_direct_immutable:
  extend_place cx pv sub st = (INL (PlaceR (ImmutablePlace src id [])),rt) ==> F
Proof
  Cases_on `pv` >> Cases_on `sub` >>
  simp[oneline extend_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[bind_def, return_def, raise_def, lift_sum_def,
      value_type_CASE_rator, place_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs(), extend_memory_place_def] >>
  metis_tac[extend_storage_place_not_immutable]
QED

Theorem get_place_success_eq:
  get_place pv st = (INL p,rt) <=> pv = PlaceR p /\ rt = st
Proof
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def] >> metis_tac[]
QED

Theorem mutable_target_not_direct_immutable:
  target_mutable env bt /\ well_typed_target env bt ty /\ env_consistent env cx st /\
  eval_target_place cx bt st = (INL p,rt) ==>
  !src id. p <> ImmutablePlace src id []
Proof
  strip_tac >> qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_place_success_eq, AllCaseEqs()] >>
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `bt` >> gvs[well_typed_target_def]
  >- gvs[Once evaluate_def, get_place_def, bind_def, get_scopes_def, lift_option_type_def,
         type_check_def, assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()]
  >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      drule_all type_place_target_global_lookup >> strip_tac >>
      fs[target_mutable_def] >>
      drule_all env_consistent_toplevel_storage_static >> strip_tac >>
      gvs[Once evaluate_def, get_place_def, lookup_global_def, bind_def, lift_option_type_def,
          return_def, raise_def, IS_SOME_EXISTS]) >>
  gvs[Once evaluate_def, bind_def, get_place_success_eq, AllCaseEqs()] >>
  metis_tac[extend_place_not_direct_immutable]
QED

Theorem abi_place_operand_observations:
  abi_place_operand cx p st = (res,rt) ==>
  rt.scopes = st.scopes /\ rt.immutables = st.immutables /\ rt.accounts = st.accounts
Proof
  strip_tac >>
  `state_rel_frame (\s t. t.scopes = s.scopes /\ t.immutables = s.immutables /\
                          t.accounts = s.accounts) (abi_place_operand cx p)` by
    (irule state_rel_frame_abi_place >> simp[] >> metis_tac[]) >>
  fs[state_rel_frame_def] >> first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem abi_place_operand_valid:
  state_well_typed st /\ env_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV et (Dynamic n)) /\
  (!src id. p <> ImmutablePlace src id []) /\
  abi_place_operand cx p st = (res,rt) ==>
  state_well_typed rt /\ env_consistent env cx rt /\ rt.accounts = st.accounts /\
  no_type_error_result res /\
  case res of INL arg => abi_operand_valid rt (ArrayTV et (Dynamic n)) arg /\
                        (~?v. arg = AbiSnapshot v) | INR _ => T
Proof
  strip_tac >> Cases_on `p`
  >- gvs[abi_place_operand_def, return_def, runtime_place_typed_storage,
         abi_operand_valid_def, no_type_error_result_def]
  >- (gvs[runtime_place_typed_memory] >>
      `well_formed_type_value entry.type` by
        (irule lookup_scopes_well_typed_type >> goal_assum drule >>
         fs[state_well_typed_def]) >>
      `value_has_type entry.type entry.value` by
        (irule lookup_scopes_well_typed_value_has_type >> goal_assum drule >> fs[state_well_typed_def]) >>
      gvs[abi_place_operand_def] >>
      drule_all lookup_abi_memory_place_valid >> strip_tac >>
      Cases_on `res` >> gvs[]) >>
  gvs[runtime_place_typed_immutable] >>
  drule_all get_immutables_success_typed >> strip_tac >>
  drule subscripts_array_not_primitive >> strip_tac >>
  drule_all lookup_abi_immutable_location >> strip_tac >>
  rename1 `ImmutablePlace src id path` >> Cases_on `path` >> gvs[] >>
  gvs[abi_place_operand_def, bind_def] >>
  drule_all (SRULE [] project_abi_path_valid) >> strip_tac >> Cases_on `res` >> gvs[]
QED
