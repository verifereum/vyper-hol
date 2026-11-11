(*
 * The facts an augmented assignment to a field or element of a place needs
 * from the body simulation's premises (#637): the target's case judgment
 * from body_base_target_ok, its indices' expr_body_pre, that a supported
 * target's root is not an immutable, and what kind of place it evaluates to.
 *
 * TOP-LEVEL:
 *   aug_place_body_target_sim — target_sim from body_base_target_ok
 *   aug_place_target_indices_pre — the indices' expr_body_pre
 *)
Theory bodyAugPlaceTarget
Ancestors
  valueEncodingProps
  targetPlaceLive exprSimSource bodyExprPreFacts exprSimTopLevelProps stmtSimBreak stmtSimContinue stmtSimExpr stmtSimSeqEnv stmtSimPass stmtSimProps exprSimHypsDefs stmtSimZero stmtSimDefs loweringPosts bodyAppendStorageFacts bodyAppendStorageAdapter
  vyperStorageLayoutSafety vyperLookupStorage
  list finite_map bodySim allocLimits allocLimitsProps  exprSimHyps exprLoweringProps
  stmtSimIf stmtLoweringMono stmtLowering compileEnv fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage stmtSimReasonCode supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  exprReasonOperand
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple
  vyperTypeEnvPreservation bodySimExprCases bodyStoragePreservation
  vyperCallOutcomeStorage vyperTypeStoragePreservation
  stmtSimAssignStorage supportedDecls vyperTypeContractStaticMaps
  vyperTypeContract compileVyper supportedTypes stmtSimAssignAttr
  stmtSimAssignStorageCopy
  stmtSimAugAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignStorage
  stmtSimAugAssignAttrStorage stmtSimAssignMem stmtSimAssignTupleMem
  stmtSimAssignTupleTargets
  memoryLocalRhsProps stmtPoppedKeys exprOpenMain bodyStorageMetadata
  vyperPureExpr targetPlaceSim targetPlaceSimCases exprSimDefs
  stmtSimAugAssignPlace bodySimAugPlaceLoad bodySimAugPlaceLive
Libs
  monadsyntax

Theorem aug_place_body_target_idx:
  !t cx tops ctx func cenv.
    body_base_target_ok cx t /\ body_inv tops ctx cenv cx ==>
    target_idx_case F ctx func cenv cx t
Proof
  `(!e:expr. T) /\ !t cx tops ctx func cenv.
     body_base_target_ok cx t /\ body_inv tops ctx cenv cx ==>
     target_idx_case F ctx func cenv cx t` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[body_base_target_ok_def, target_idx_case_def] >>
  metis_tac[body_expr_ok_case]
QED

Theorem aug_place_body_target_sim:
  !t cx tops ctx func cenv env es.
    body_base_target_ok cx t /\ body_inv tops ctx cenv cx /\
    target_pre cenv cx env t es ==>
    target_sim ctx func cenv cx env t es
Proof
  rpt strip_tac >>
  `target_idx_case F ctx func cenv cx t` by
    metis_tac[aug_place_body_target_idx] >>
  drule target_case_all >> simp[target_case_def] >>
  disch_then irule >> simp[]
QED

Theorem aug_place_supported_root:
  !t pt nsid.
    supported_target_info tops bindings t = SOME pt /\
    target_root t = TopLevelNameTarget nsid ==>
    supported_place_root tops nsid
Proof
  `(!e:expr. T) /\ (!t. !pt nsid.
    supported_target_info tops bindings t = SOME pt /\
    target_root t = TopLevelNameTarget nsid ==>
    supported_place_root tops nsid)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_root_def, supportedTargetsTheory.supported_target_info_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem aug_place_supported_root_namespace:
  supported_place_root tops (src,id) ==> src = NONE
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule supportedDeclsTheory.supported_lookup_other_module >>
  strip_tac >> gvs[supportedExprFormsTheory.supported_place_root_def]
QED

Theorem aug_place_supported_root_decl:
  !tops id.
    ((?vis mut ty slot.
       supported_variable_decl tops (NONE,id) = SOME (vis,mut,ty,slot) /\
       (mut = Storage \/ mut = Transient)) \/
     (?vis tr kt vt slot.
       supported_hashmap_decl tops (NONE,id) = SOME (vis,tr,kt,vt,slot))) ==>
    IS_SOME (find_var_decl_by_name id tops)
Proof
  Induct >> simp[supportedDeclsTheory.supported_variable_decl_def,
    supportedDeclsTheory.supported_hashmap_decl_def] >>
  Cases_on `h` >>
  simp[find_var_decl_by_name_def,
    supportedDeclsTheory.supported_variable_decl_def,
    supportedDeclsTheory.supported_hashmap_decl_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem aug_place_supported_root_not_immutable:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings t = SOME pt ==>
  ~immutable_root cx t
Proof
  strip_tac >> simp[immutable_root_def] >> rpt strip_tac >>
  `supported_place_root tops (src,id)` by metis_tac[aug_place_supported_root] >>
  drule aug_place_supported_root_namespace >> strip_tac >> gvs[] >>
  `ts = tops` by gvs[body_inv_def, vyperContextTheory.get_module_code_def] >>
  gvs[] >>
  `IS_SOME (find_var_decl_by_name id tops)` suffices_by simp[] >>
  irule aug_place_supported_root_decl >>
  gvs[supportedExprFormsTheory.supported_place_root_def] >>
  Cases_on `supported_variable_decl tops (NONE,id)`
  >- (gvs[] >> Cases_on `supported_hashmap_decl tops (NONE,id)` >> gvs[] >>
      rename1 `supported_hashmap_decl tops (NONE,id) = SOME mdecl` >>
      PairCases_on `mdecl` >> simp[]) >>
  rename1 `supported_variable_decl tops (NONE,id) = SOME vdecl` >>
  PairCases_on `vdecl` >> gvs[] >>
  Cases_on `vdecl1` >> Cases_on `vdecl3` >> gvs[] >>
  Cases_on `vdecl0` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_target_indices_pre:
  !t.
    ~supported_target_exists expr_evm_run_root t /\
    ~supported_target_exists call_operands_effect_root t /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t) /\
    EVERY (\e. ~is_extcode e) (target_indices t) /\
    IS_SOME (type_place_target env t) /\
    IS_SOME (supported_target_info tops bindings t) /\
    ~supported_target_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
    call_evaluation_safe cx (int_calls_target t) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) t ==>
              occurs_abi_decode_target target tops) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env tops) target)) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    target_indices_pre cenv cx env t
Proof
  `(!e:expr. T) /\ (!t.
    ~supported_target_exists expr_evm_run_root t /\
    ~supported_target_exists call_operands_effect_root t /\
    EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal)) (int_calls_target t) /\
    EVERY (\e. ~is_extcode e) (target_indices t) /\
    IS_SOME (type_place_target env t) /\
    IS_SOME (supported_target_info tops bindings t) /\
    ~supported_target_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) t /\
    call_evaluation_safe cx (int_calls_target t) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) t ==>
              occurs_abi_decode_target target tops) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env tops) target)) /\
    supported_program tops /\ get_module_code cx NONE = SOME tops ==>
    target_indices_pre cenv cx env t)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_indices_pre_def, supported_expr_exists_def, int_calls_expr_def, target_indices_def, EVERY_APPEND, EVERY_CONJ,
       GSYM expr_has_evm_run_def] >>
  rpt conj_tac >> rpt gen_tac
  >~ [`IS_SOME (type_place_target env (SubscriptTarget t e))`]
    >- suspend "subscript"
  >> suspend "attribute"
QED

Resume aug_place_target_indices_pre[attribute]:
  simp[Once well_typed_expr_def, supportedTargetsTheory.supported_target_info_def] >>
  Cases_on `type_place_target env t` >> simp[] >>
  Cases_on `supported_target_info tops bindings t` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Resume aug_place_target_indices_pre[subscript]:
  simp[Once well_typed_expr_def, supportedTargetsTheory.supported_target_info_def] >>
  Cases_on `well_typed_expr env e` >> simp[] >>
  Cases_on `type_place_target env t` >> simp[] >>
  Cases_on `supportedExprs$supported_expr tops e` >> simp[] >>
  Cases_on `supported_target_info tops bindings t` >> simp[] >>
  rpt strip_tac
  >- (first_x_assum irule >> simp[] >>
      metis_tac[call_evaluation_safe_append_left]) >>
  irule stmt_expr_body_pre >>
  simp[gasContextTheory.cx_tops_def] >>
  metis_tac[call_evaluation_safe_append_right, APPEND_NIL]
QED

Finalise aug_place_target_indices_pre

Theorem aug_place_supported_indices:
  !t. IS_SOME (supported_target_info tops bindings t) ==>
    !e. MEM e (target_indices t) ==> supportedExprs$supported_expr tops e
Proof
  `(!e:expr. T) /\ (!t.
    IS_SOME (supported_target_info tops bindings t) ==>
    !e. MEM e (target_indices t) ==> supportedExprs$supported_expr tops e)`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_indices_def, supportedTargetsTheory.supported_target_info_def] >>
  rpt conj_tac >> rpt gen_tac >>
  Cases_on `supported_target_info tops bindings t` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `supportedExprs$supported_expr tops e` >> gvs[] >> metis_tac[]
QED


Theorem aug_place_hashmap_build:
  !tops src id vis tr kt vt slot.
    supported_hashmap_decl tops (src,id) = SOME (vis,tr,kt,vt,slot) ==>
    src = NONE /\ build_hashmap_info tops (src,id) = SOME (tr,kt,vt)
Proof
  Induct >> simp[supported_hashmap_decl_def] >> Cases >>
  rw[supported_hashmap_decl_def, build_hashmap_info_def] >> metis_tac[]
QED

Theorem aug_place_variable_excludes_hashmap:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_variable_decl tops nsid = SOME (vis,mut,ty,slot) ==>
  supported_hashmap_decl tops nsid = NONE
Proof
  Cases_on `nsid` >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  drule_all build_maps_variable >> strip_tac >>
  Cases_on `supported_hashmap_decl tops (NONE,r)` >> simp[] >>
  rename1 `supported_hashmap_decl tops (NONE,r) = SOME d` >>
  PairCases_on `d` >> drule aug_place_hashmap_build >> simp[]
QED

Theorem aug_place_legacy_field_info:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_storage_field_write tops id fld ==>
  IS_SOME (supported_target_info tops bindings
    (AttributeTarget (TopLevelNameTarget id) fld))
Proof
  simp[supported_storage_field_write_def, supportedExprFormsTheory.supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops id` >> simp[] >>
  rename1 `supported_variable_decl tops id = SOME d` >> PairCases_on `d` >>
  Cases_on `d0` >> Cases_on `d1` >> Cases_on `d2` >> Cases_on `d3` >>
  simp[] >> rpt strip_tac >>
  `supported_hashmap_decl tops id = NONE` by
    metis_tac[aug_place_variable_excludes_hashmap] >>
  gvs[supportedTargetsTheory.supported_target_info_def,
      supportedExprFormsTheory.supported_place_root_def, AllCaseEqs()] >>
  Cases_on `supported_storage_type tops (StructT p)` >> gvs[] >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  Cases_on `ALOOKUP x' fld` >> gvs[alistTheory.ALOOKUP_NONE]
QED

Theorem aug_place_legacy_subscript_info:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supportedExprForms$supported_subscript_base tops id /\
  supportedExprs$supported_expr tops key ==>
  IS_SOME (supported_target_info tops bindings
    (SubscriptTarget (TopLevelNameTarget id) key))
Proof
  simp[supportedExprFormsTheory.supported_subscript_base_def] >>
  strip_tac
  >- suspend "array"
  >> suspend "map"
QED

Resume aug_place_legacy_subscript_info[array]:
  qpat_x_assum `supported_storage_array _ _` mp_tac >>
  simp[supportedExprFormsTheory.supported_storage_array_def] >>
  Cases_on `supported_variable_decl tops id` >> simp[] >>
  rename1 `supported_variable_decl tops id = SOME d` >> PairCases_on `d` >>
  Cases_on `d0` >> Cases_on `d1` >> Cases_on `d2` >> Cases_on `d3` >>
  simp[] >> strip_tac >>
  `supported_hashmap_decl tops id = NONE` by
    metis_tac[aug_place_variable_excludes_hashmap] >>
  simp[supportedTargetsTheory.supported_target_info_def,
       supportedExprFormsTheory.supported_place_root_def]
QED

Resume aug_place_legacy_subscript_info[map]:
  Cases_on `supported_hashmap_decl tops id` >> gvs[] >>
  rename1 `supported_hashmap_decl tops id = SOME d` >> PairCases_on `d` >>
  Cases_on `d0` >> Cases_on `d4` >> gvs[] >>
  `supported_variable_decl tops id = NONE` by
    (Cases_on `supported_variable_decl tops id` >> simp[] >>
     rename1 `supported_variable_decl tops id = SOME v` >> PairCases_on `v` >>
     metis_tac[aug_place_variable_excludes_hashmap, optionTheory.NOT_SOME_NONE]) >>
  simp[supportedTargetsTheory.supported_target_info_def,
       supportedExprFormsTheory.supported_place_root_def]
QED

Finalise aug_place_legacy_subscript_info

Theorem aug_place_supported_stmt_target_info:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) ==>
  ?pt. supported_target_info tops bindings t = SOME pt
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    gvs[body_inv_def] >>
  `IS_SOME (supported_target_info tops bindings t)` suffices_by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  qpat_x_assum `supported_stmt _ _ _` mp_tac >>
  simp[supportedStmtsTheory.supported_stmt_def] >> strip_tac
  >- (gvs[supportedStmtsTheory.supported_target_def] >>
      Cases_on `bt` >> gvs[] >>
      metis_tac[aug_place_legacy_field_info, aug_place_legacy_subscript_info])
  >- (Cases_on `supported_target_info tops bindings (AttributeTarget bt fld)` >>
      gvs[supported_aug_target_def] >> pairarg_tac >> gvs[])
  >- (gvs[supportedStmtsTheory.supported_target_def] >>
      Cases_on `bt` >> gvs[] >>
      metis_tac[aug_place_legacy_subscript_info])
  >> Cases_on `supported_target_info tops bindings (SubscriptTarget bt k)` >>
     gvs[supported_aug_target_def] >> pairarg_tac >> gvs[]
QED

Theorem aug_place_extend_immutable_origin:
  !pv sb cx s mid id path st.
    extend_place cx pv sb s = (INL (PlaceR (ImmutablePlace mid id path)),st) ==>
    ?old. pv = PlaceR (ImmutablePlace mid id old)
Proof
  Cases
  >- simp[extend_place_def, raise_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def,
           extend_memory_place_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule vyperStoragePlaceProvenanceTheory.extend_storage_place_subregion >>
      simp[])
  >> Cases_on `sb` >>
  simp[extend_place_def, bind_def, ignore_bind_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[value_type_CASE_rator, bind_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem aug_place_global_immutable_origin:
  lookup_global cx src name s = (INL (PlaceR (ImmutablePlace mid id path)),st) ==>
  ?ts. get_module_code cx src = SOME ts /\
       find_var_decl_by_name name ts = NONE
Proof
  simp[lookup_global_def, bind_def, lift_option_type_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
       var_decl_info_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[bind_def, lift_option_type_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem aug_place_base_immutable_origin:
  !t cx s mid id path st.
    eval_base_place cx t s = (INL (PlaceR (ImmutablePlace mid id path)),st) ==>
    immutable_root cx t
Proof
  `(!e:expr. T) /\ (!t. !cx s mid id path st.
    eval_base_place cx t s = (INL (PlaceR (ImmutablePlace mid id path)),st) ==>
    immutable_root cx t)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >- (PairCases_on `p` >> simp[Once evaluate_def] >> strip_tac >>
      drule aug_place_global_immutable_origin >>
      simp[immutable_root_def, target_root_def])
  >> rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule aug_place_extend_immutable_origin >> strip_tac >> gvs[] >>
  simp[immutable_root_def, target_root_def] >>
  first_x_assum drule >> simp[immutable_root_def]
QED

Theorem aug_place_supported_success_kind:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings t = SOME pt /\
  eval_target_place cx t es = (INL p,st) ==>
  ((?id path. p = MemoryPlace id path) \/
   (?tr slot tv. p = StoragePlace tr slot tv))
Proof
  rpt strip_tac >> Cases_on `p` >> simp[] >>
  `~immutable_root cx t` by metis_tac[aug_place_supported_root_not_immutable] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[aug_place_base_immutable_origin]
QED

