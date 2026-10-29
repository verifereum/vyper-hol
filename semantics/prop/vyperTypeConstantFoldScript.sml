(*
 * Soundness of the checker's constants fold against deployment.
 *
 * TOP-LEVEL:
 * - constant_value_eval_expr
 * - constants_fold_evaluate_module_constants
 * - check_contract_evaluate_all_constants
 * - contract_namespaces_ok_constants_order
 *
 * Helper:
 * - get_tenv_constant_context, get_tenv_sources
 * - evaluate_builtin_constant_context, evaluate_type_builtin_constant_context
 * - constant_length_result_array_length, merge_constants_immutables
 * - constants_fold_module_constants_env
 *)

Theory vyperTypeConstantFold
Ancestors
  list finite_map alist option pair sorting
  vyperAST vyperValue vyperState vyperContext vyperInterpreter
  vyperTypeContract vyperTypeConstantCells vyperTypeInvariants
  vyperTypeSystem vyperTypeValues vyperTypeExprSoundness
  vyperTypeInitialState vyperTyping vyperMisc vyperPlaceResultTyping
  vyperTypeContractStaticMaps vyperTypeBuiltins

(* ===== Context independence of constant builtins ===== *)

Theorem get_tenv_constant_context:
  get_tenv (constant_context mods) = type_env_all_modules mods
Proof
  simp[get_tenv_def, constant_context_def]
QED

(* Helper: the constant builtins read the context only through get_tenv, and
   never the accounts. *)
Theorem evaluate_builtin_constant_context:
  !bt cx mods acc ty tys vs.
  constant_builtin bt /\ get_tenv cx = type_env_all_modules mods ==>
  evaluate_builtin cx acc ty bt tys vs =
  evaluate_builtin (constant_context mods) empty_accounts ty bt tys vs
Proof
  rpt gen_tac >> Cases_on `bt` >>
  simp[constant_builtin_def] >>
  simp[evaluate_builtin_def, get_tenv_constant_context]
QED

Theorem evaluate_type_builtin_constant_context:
  !tb cx mods typ tys vs.
  constant_type_builtin tb /\ get_tenv cx = type_env_all_modules mods ==>
  evaluate_type_builtin cx tb typ tys vs =
  evaluate_type_builtin (constant_context mods) tb typ tys vs
Proof
  rpt gen_tac >> Cases_on `tb` >> simp[constant_type_builtin_def] >>
  Cases_on `vs` >>
  simp[evaluate_type_builtin_def, get_tenv_constant_context]
QED

Theorem constant_length_result_array_length:
  !v n cx st.
  constant_length v = SOME n ==>
  result_array_length cx (Value v) st = (INL n, st)
Proof
  rpt gen_tac >> Cases_on `v` >>
  simp[constant_length_def, result_array_length_def, read_result_def,
       bind_def, return_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  simp[constant_length_def, result_array_length_def, read_result_def,
       bind_def, return_def]
QED

Definition constant_result_shape_def:
  constant_result_shape pv <=>
    (?v. pv = Value v) \/
    (?src id path. pv = PlaceR (ImmutablePlace src id path))
End

Theorem constant_result_length[local]:
  constant_result_shape pv /\ read_result cx pv st = (INL v,st) /\
  constant_length v = SOME n ==>
  result_array_length cx pv st = (INL n,st)
Proof
  rw[constant_result_shape_def] >>
  gvs[result_array_length_def, bind_def, read_result_def, return_def] >>
  Cases_on `v` >> gvs[constant_length_def, return_def] >>
  rename1 `constant_length (ArrayV av)` >> Cases_on `av` >> gvs[constant_length_def, return_def]
QED

Theorem constant_result_selection[local]:
  constant_result_shape pv /\
  eval_result_typed (env,cx,st) pv (Type ty) /\
  read_result cx pv st = (INL v,st) /\
  env.type_defs = get_tenv cx /\
  evaluate_type env.type_defs ty = SOME tv /\
  subscript_type tv sb = SOME etv /\
  evaluate_type env.type_defs result_ty = SOME etv /\
  evaluate_subscripts tv v [sb] = INL w ==>
  ?out. select_result cx ty pv sb st = (INL out,st) /\
    constant_result_shape out /\
    eval_result_typed (env,cx,st) out (Type result_ty) /\
    read_result cx out st = (INL w,st)
Proof
  rw[constant_result_shape_def]
  >- (qexists `Value w` >>
      gvs[eval_result_typed_def, read_result_def, return_def] >>
      simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
           return_def, read_result_def] >>
      irule vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
      qexistsl [`v`,`[sb]`,`tv`] >> simp[subscripts_type_def] >>
      metis_tac[evaluate_type_well_formed_type_value]) >>
  qexists `PlaceR (ImmutablePlace src id (path ++ [sb]))` >>
  gvs[eval_result_typed_def, runtime_place_typed_def] >>
  `read_place cx (ImmutablePlace src id path) st = (INL v,st)` by
    gvs[read_result_def] >>
  conj_tac
  >- simp[select_result_def, extend_place_def, bind_def, ignore_bind_def,
          lift_sum_def, return_def, extend_memory_place_def] >>
  `well_formed_type_value etv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  gvs[place_type_value_def, read_result_def, read_place_def,
      bind_def, lift_option_type_def, lift_sum_def, return_def,
      AllCaseEqs()] >>
  gvs[get_immutables_def, get_address_immutables_def, bind_def,
      lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[option_CASE_rator, sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  conj_tac
  >- (drule vyperPlaceResultTypingTheory.subscripts_type_append >>
      disch_then (qspec_then `[sb]` mp_tac) >> simp[subscripts_type_def]) >>
  drule_all evaluate_subscripts_append >> simp[]
QED

Theorem constant_immutable_read_inv:
  read_result cx (PlaceR (ImmutablePlace src id path)) st = (INL v,st') ==>
  st' = st /\
  ?imms tv root.
    ALOOKUP st.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,root) /\
    evaluate_subscripts tv root path = INL v
Proof
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def] >>
  strip_tac >>
  gvs[option_CASE_rator, sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  PairCases_on `tva` >> gvs[]
QED

Theorem constant_result_length_inv:
  constant_result_shape pv /\
  result_array_length cx pv st = (INL n,st') ==>
  st' = st /\ ?v. read_result cx pv st = (INL v,st) /\
    constant_length v = SOME n
Proof
  strip_tac >> fs[constant_result_shape_def]
  >- gvs[result_array_length_def, read_result_def, bind_def, return_def,
         value_CASE_rator, array_value_CASE_rator, raise_def,
         constant_length_def, AllCaseEqs()] >>
  gvs[result_array_length_def, read_result_def, bind_def,
      sum_CASE_rator, AllCaseEqs()] >>
  qpat_assum `read_place _ _ _ = _` mp_tac >>
  drule vyperPlaceTypingTheory.read_place_preserves_state >>
  strip_tac >> simp[] >> strip_tac >>
  gvs[value_CASE_rator, array_value_CASE_rator, return_def, raise_def,
      constant_length_def, AllCaseEqs()]
QED

Theorem constant_result_selection_inv:
  constant_result_shape pv /\
  eval_result_typed (env,cx,st) pv (Type ty) /\
  evaluate_type env.type_defs ty = SOME tv /\
  env.type_defs = get_tenv cx /\
  select_result cx ty pv sb st = (INL out,st1) /\
  read_result cx out st1 = (INL w,st2) ==>
  st1 = st /\ st2 = st /\
  ?v. read_result cx pv st = (INL v,st) /\
    evaluate_subscripts tv v [sb] = INL w
Proof
  strip_tac >> fs[constant_result_shape_def]
  >- gvs[select_result_def, read_result_def, eval_result_typed_def,
         bind_def, lift_option_type_def, lift_sum_def, return_def,
         option_CASE_rator, sum_CASE_rator, raise_def, AllCaseEqs()] >>
  gvs[eval_result_typed_def, runtime_place_typed_def] >>
  gvs[select_result_def, extend_place_def, extend_memory_place_def,
      bind_def, ignore_bind_def, lift_sum_def, return_def,
      sum_CASE_rator, AllCaseEqs()] >>
  gvs[place_type_value_def, read_result_def, read_place_def,
      bind_def, lift_option_type_def, lift_sum_def, return_def,
      AllCaseEqs()] >>
  gvs[get_immutables_def, get_address_immutables_def, bind_def,
      lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[option_CASE_rator, sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  drule_all evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` mp_tac) >> simp[]
QED

Theorem constant_result_selection_base[local]:
  constant_result_shape pv /\
  select_result cx ty pv sb st = (INL out,st') ==>
  st' = st /\ constant_result_shape out /\
  ?v. read_result cx pv st = (INL v,st)
Proof
  strip_tac >> fs[constant_result_shape_def]
  >- gvs[select_result_def, read_result_def, constant_result_shape_def,
         bind_def, lift_option_type_def, lift_sum_def, return_def,
         option_CASE_rator, sum_CASE_rator, raise_def, AllCaseEqs()] >>
  gvs[select_result_def, extend_place_def, extend_memory_place_def,
      bind_def, ignore_bind_def, lift_sum_def, return_def,
      sum_CASE_rator, AllCaseEqs()] >>
  drule place_type_value_state >>
  strip_tac >> gvs[] >>
  drule vyperPlaceTypingTheory.read_place_preserves_state >>
  strip_tac >> gvs[read_result_def, constant_result_shape_def, raise_def]
QED

(* ===== Expression soundness ===== *)

Theorem get_tenv_sources:
  ALOOKUP cx.sources cx.txn.target = SOME mods ==>
  get_tenv cx = type_env_all_modules mods
Proof
  simp[get_tenv_def]
QED

Theorem checked_constant_name_result[local]:
  check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist) checker_addr mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP am.immutables cx.txn.target = SOME imms /\
  deployment_constant_cells_typed (type_env_all_modules mods)
    cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src)
    (TopLevelName ann (src,id)) /\
  constant_expr mods (TopLevelName ann (src,id)) /\
  constant_value mods imms (TopLevelName ann (src,id)) = SOME v ==>
  ?pv. eval_expr cx (TopLevelName ann (src,id)) (initial_state am sc) =
         (INL pv,initial_state am sc) /\
    eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
      pv (Type ann) /\
    read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
    value_runtime_typed (artifact_env artifact mods current_src) ann v /\
    constant_result_shape pv
Proof
  rw[constant_expr_def, declared_constant_def] >>
  `ann = ty` by (irule checked_constant_declared_type >> metis_tac[]) >>
  gvs[constant_value_def, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  `evaluate_type (type_env_all_modules mods) ann = SOME z0 /\
   value_has_type z0 z1` by
    (gvs[deployment_constant_cells_typed_def] >> metis_tac[]) >>
  qexists `PlaceR (ImmutablePlace src id [])` >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       get_tenv_def, get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_option_type_def, initial_state_def,
       eval_result_typed_def, runtime_place_typed_def, place_type_value_def,
       read_result_def, read_place_def, lift_sum_def, subscripts_type_def,
       evaluate_subscripts_def, value_runtime_typed_def, artifact_env_def,
       constant_result_shape_def] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem constant_values_runtime_types[local]:
  !es vs. LIST_REL (\e v. value_runtime_typed env (expr_type e) v) es vs ==>
  exprs_runtime_typed env es vs
Proof
  Induct >> Cases_on `vs` >>
  gvs[exprs_runtime_typed_def, value_runtime_typed_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists `tv::tvs` >> simp[]
QED

Theorem constant_struct_names_typed[local]:
  !names tvs vs.
    LENGTH names = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    LIST_REL value_has_type tvs vs ==>
    struct_has_type (ZIP (names,tvs)) (ZIP (names,vs))
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[Once value_has_type_def]
QED

Theorem constant_expr_types_OPT_MMAP[local]:
  !kes tvs.
    LIST_REL (\e tv. evaluate_type tenv (expr_type e) = SOME tv)
      (MAP SND kes) tvs ==>
    OPT_MMAP (evaluate_type tenv) (MAP (expr_type o SND) kes) = SOME tvs
Proof
  Induct >> Cases_on `tvs` >> simp[OPT_MMAP_def] >>
  PairCases_on `h` >> simp[OPT_MMAP_def]
QED

Theorem constant_types_OPT_MMAP_mono[local]:
  !types tenv nid tvs.
    OPT_MMAP (evaluate_type (tenv \\ nid)) types = SOME tvs ==>
    OPT_MMAP (evaluate_type tenv) types = SOME tvs
Proof
  Induct >> simp[OPT_MMAP_def] >> rpt gen_tac >>
  Cases_on `evaluate_type (tenv \\ nid) h` >> simp[] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nid)) types` >> simp[] >>
  strip_tac >> gvs[] >> drule (cj 1 evaluate_type_mono) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem constant_struct_value_typed[local]:
  well_typed_expr env (StructLit ty sid kes) /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v)
    (MAP SND kes) vs ==>
  value_runtime_typed env ty (StructV (ZIP (MAP FST kes,vs)))
Proof
  strip_tac >> drule constant_values_runtime_types >>
  rw[exprs_runtime_typed_def, value_runtime_typed_def] >>
  gvs[well_typed_expr_def, well_formed_type_def, IS_SOME_EXISTS] >>
  qpat_x_assum `evaluate_type _ (StructT _) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  strip_tac >> gvs[value_has_type_def] >>
  drule constant_expr_types_OPT_MMAP >>
  qpat_x_assum `MAP (expr_type o SND) kes = MAP SND args` (assume_tac o GSYM) >>
  gvs[] >>
  drule constant_types_OPT_MMAP_mono >> strip_tac >> gvs[] >>
  strip_tac >> gvs[] >> irule constant_struct_names_typed >>
  imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_MAP] >>
  metis_tac[LENGTH_MAP]
QED

Theorem constant_named_exprs_typed[local]:
  !env kes. well_typed_named_exprs env kes ==> well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Theorem checked_constant_decl_typed[local]:
  check_contract mode layouts target mods = SOME artifact /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  assignable_type (type_env_all_modules mods) ty /\
  well_typed_expr (artifact_env artifact mods src) e /\
  expr_type e = ty /\ constant_expr mods e
Proof
  rpt strip_tac >> drule check_contract_toplevel_decl_MEM_checked >>
  disch_then drule >> disch_then drule >> simp[check_toplevel_decl_def]
QED

Theorem constant_place_expr_well_typed[local]:
  check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist) checker_addr mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods ==>
  !e vt. constant_expr mods e /\
    type_place_expr (artifact_env artifact mods current_src) e = SOME vt ==>
    ?ty. vt = Type ty /\
      well_typed_expr (artifact_env artifact mods current_src) e /\
      well_formed_type (type_env_all_modules mods) ty
Proof
  strip_tac >>
  (* Explicit mutual principle: pinned HOL#2115 breaks generic Induct. *)
  ho_match_mp_tac
    (expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |> SIMP_RULE (srw_ss()) []) >>
  rw[constant_expr_def] >> fs[Once well_typed_expr_def]
  >- (PairCases_on `p` >>
      gvs[constant_expr_def, declared_constant_def] >>
      `contract_namespaces_ok F mods` by
        metis_tac[check_contract_runtime_namespaces] >>
      `ALOOKUP mods p0 = SOME tls` by
        (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[contract_namespaces_ok_def]) >>
      `assignable_type (type_env_all_modules mods) ty` by
        metis_tac[checked_constant_decl_typed] >>
      `toplevel_vtypes_complete artifact.cta_toplevel_vtypes
          (initial_evaluation_context cx.sources cx.layouts cx.txn p0)` by
        (irule check_contract_toplevel_vtypes_complete_checked >> metis_tac[]) >>
      `FLOOKUP artifact.cta_toplevel_vtypes (p0,p1) = SOME (Type ty)` by
        (gvs[toplevel_vtypes_complete_def] >>
         first_x_assum irule >>
         simp[get_module_code_def, initial_evaluation_context_def] >> metis_tac[]) >>
      gvs[artifact_env_def, vtype_annotation_ok_def, well_typed_expr_def] >>
      Cases_on `t` >> gvs[assignable_type_def] >>
      Cases_on `FLOOKUP (type_env_all_modules mods) p` >>
      gvs[] >> Cases_on `x` >> gvs[])
  >- (Cases_on `type_place_expr (artifact_env artifact mods current_src) e` >>
      gvs[] >> rename1 `type_place_expr _ e = SOME (Type base_ty)` >>
      Cases_on `base_ty` >>
      gvs[subscript_vtype_def, vtype_annotation_ok_def, well_typed_expr_def,
          subscript_type_ok_def, well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `evaluate_type (type_env_all_modules mods) t` >>
      gvs[artifact_env_def])
QED

Theorem constant_subscript_base_well_typed[local]:
  check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist) checker_addr mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  constant_expr mods e /\
  well_typed_expr (artifact_env artifact mods current_src) (Subscript ty e ix) ==>
  well_typed_expr (artifact_env artifact mods current_src) e
Proof
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def] >> metis_tac[constant_place_expr_well_typed]
QED

(* Checked constant folding agrees with resolution and explicit reads. *)
Theorem constant_place_annotation[local]:
  !env e vt. type_place_expr env e = SOME vt ==>
    vtype_annotation_ok vt (expr_type e)
Proof
  Cases_on `e` >> simp[expr_type_def] >> rpt strip_tac >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()]
  >- (Cases_on `p` >>
      simp[Once well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()]) >>
  metis_tac[]
QED

Theorem constant_subscript_type_ok[local]:
  well_typed_expr env (Subscript ty e1 e2) /\
  well_typed_expr env e1 ==>
  subscript_type_ok (expr_type e1) e2 ty
Proof
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  drule constant_place_annotation >> strip_tac >>
  Cases_on `vt` >> gvs[vtype_annotation_ok_def, subscript_vtype_def] >>
  Cases_on `expr_type e1` >>
  gvs[subscript_vtype_def, subscript_type_ok_def] >>
  metis_tac[vyperTypeExprResultTheory.well_typed_expr_not_hashmap_place]
QED

Theorem constant_subscript_index_matches[local]:
  subscript_type_ok ct ie ty /\ constant_value mods imms ie = SOME idx ==>
  vyperTypeExprResult$subscript_index_matches ct ie idx
Proof
  Cases_on `ct` >>
  simp[vyperTypeExprResultTheory.subscript_index_matches_def] >>
  rpt strip_tac >>
  gvs[vyperTypeExprResultTheory.subscript_type_ok_tuple] >>
  gvs[Once constant_value_def, vyperValueOperationTheory.evaluate_literal_def]
QED

Theorem constant_subscript_runtime_type[local]:
  subscript_type_ok ct ie ty /\
  vyperTypeExprResult$subscript_index_matches ct ie idx /\
  evaluate_type tenv ct = SOME tv /\
  subscript_type tv (ValueSubscript idx) = SOME etv ==>
  evaluate_type tenv ty = SOME etv
Proof
  Cases_on `ct` >> simp[subscript_type_ok_def] >> rpt strip_tac >>
  gvs[vyperTypeExprResultTheory.subscript_index_matches_def]
  >- (drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
      gvs[subscript_type_def, AllCaseEqs(), LIST_REL_EL_EQN] >>
      metis_tac[]) >>
  Cases_on `idx` >>
  gvs[Once evaluate_type_def, subscript_type_def, AllCaseEqs()]
QED

Theorem constant_subscript_selected_typed[local]:
  subscript_type_ok ct ie ty /\
  vyperTypeExprResult$subscript_index_matches ct ie idx /\
  evaluate_type env.type_defs ct = SOME tv /\ value_has_type tv base_value /\
  evaluate_subscripts tv base_value [ValueSubscript idx] = INL selected ==>
  ?etv. evaluate_type env.type_defs ty = SOME etv /\
    subscript_type tv (ValueSubscript idx) = SOME etv /\
    value_has_type etv selected
Proof
  rpt strip_tac >>
  `well_formed_type_value tv` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  drule_at (Pat `evaluate_subscripts _ _ _ = _`)
    vyperPlaceStatePreservationTheory.evaluate_subscripts_declared_type_exists >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  drule_all constant_subscript_runtime_type >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem constant_attribute_selected_typed[local]:
  attribute_type env.type_defs ct id = SOME ty /\
  evaluate_type env.type_defs ct = SOME tv /\ value_has_type tv base_value /\
  evaluate_subscripts tv base_value [AttrSubscript id] = INL selected ==>
  ?etv. evaluate_type env.type_defs ty = SOME etv /\
    subscript_type tv (AttrSubscript id) = SOME etv /\
    value_has_type etv selected
Proof
  rpt strip_tac >> drule_all attribute_type_runtime_step >> strip_tac >>
  `well_formed_type_value tv` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  `subscripts_type tv [AttrSubscript id] = SOME field_tv` by
    simp[subscripts_type_def] >>
  drule_at (Pat `evaluate_subscripts _ _ _ = _`)
    vyperPlaceStatePreservationTheory.evaluate_subscripts_type_metadata >>
  disch_then (qspec_then `tv` mp_tac) >> simp[] >>
  metis_tac[]
QED

Theorem constant_context_well_typed[local]:
  context_well_typed (constant_context mods)
Proof
  simp[context_well_typed_def, constant_context_def,
       empty_evaluation_context_def] >> EVAL_TAC
QED

Theorem constant_empty_accounts_well_typed[local]:
  accounts_well_typed empty_accounts
Proof
  rw[accounts_well_typed_def, account_well_typed_def] >> EVAL_TAC
QED

Theorem constant_builtin_success_typed[local]:
  constant_builtin bt /\ bt <> Len /\
  well_typed_builtin_app ty bt ts /\
  get_tenv cx = type_env_all_modules mods /\
  MAP (evaluate_type (get_tenv cx)) ts = MAP SOME tvs /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  LIST_REL value_has_type tvs vs /\
  evaluate_builtin cx acc ty bt ts vs = INL v ==>
  value_has_type tv v
Proof
  strip_tac >>
  `evaluate_builtin (constant_context mods) empty_accounts ty bt ts vs = INL v` by
    metis_tac[evaluate_builtin_constant_context] >>
  drule_at (Pat `evaluate_builtin _ _ _ _ _ _ = _`)
    vyperTypeBuiltinsTheory.well_typed_builtin_app_success_type >>
  disch_then (qspecl_then [`tvs`, `tv`] mp_tac) >>
  simp[get_tenv_constant_context, constant_context_well_typed,
       constant_empty_accounts_well_typed] >> gvs[]
QED

Theorem constant_type_builtin_success_typed[local]:
  constant_type_builtin tb /\
  type_builtin_result_ok (get_tenv cx) tb result_ty target_ty ts /\
  well_typed_type_builtin_args tb target_ty ts /\
  evaluate_type (get_tenv cx) result_ty = SOME result_tv /\
  evaluate_type_builtin cx tb target_ty ts vs = INL v ==>
  value_has_type result_tv v
Proof
  Cases_on `tb` >> simp[constant_type_builtin_def] >>
  rw[type_builtin_result_ok_def, well_typed_type_builtin_args_def,
     evaluate_type_builtin_def, AllCaseEqs()] >>
  gvs[LENGTH_EQ_NUM_compute]
  >- (drule vyperTypeDefaultsTheory.default_value_has_type_thm >> simp[])
  >- metis_tac[vyperTypeConversionsTheory.evaluate_max_value_well_typed]
  >- metis_tac[vyperTypeConversionsTheory.evaluate_max_value_well_typed]
  >- metis_tac[vyperTypeConversionsTheory.evaluate_min_value_well_typed]
  >- metis_tac[vyperTypeConversionsTheory.evaluate_min_value_well_typed] >>
  Cases_on `vs` >>
  gvs[evaluate_type_def, evaluate_type_builtin_def,
      within_int_bound_def, value_has_type_def]
QED

Theorem constant_len_success_typed[local]:
  well_typed_builtin_app ty Len [arg_ty] /\
  evaluate_type env.type_defs ty = SOME tv /\
  evaluate_type env.type_defs arg_ty = SOME arg_tv /\
  value_has_type arg_tv v /\ constant_length v = SOME n ==>
  value_has_type tv (IntV (&n))
Proof
  strip_tac >>
  `result_array_length cx (Value v) st = (INL n,st)` by
    metis_tac[constant_length_result_array_length] >>
  drule_at (Pat `result_array_length _ _ _ = _`)
    vyperTypeBuiltinsTheory.Len_builtin_sound >>
  simp[value_result_typed_def] >> disch_then drule_all >> simp[]
QED

Definition constant_machine_immutables_def:
  constant_machine_immutables am addr =
    case ALOOKUP am.immutables addr of NONE => [] | SOME imms => imms
End

Theorem constant_value_eval_expr_shape[local]:
  (!mods imms e v cx am sc artifact current_src mode checker_layouts checker_addr.
     constant_value mods imms e = SOME v /\
     check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist) checker_addr mods = SOME artifact /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     constant_machine_immutables am cx.txn.target = imms /\
     deployment_constant_cells_typed (type_env_all_modules mods)
       cx.txn.target mods am /\
     well_typed_expr (artifact_env artifact mods current_src) e /\
     constant_expr mods e ==>
     ?pv. eval_expr cx e (initial_state am sc) = (INL pv,initial_state am sc) /\
       eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
         pv (Type (expr_type e)) /\
       read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
       value_runtime_typed (artifact_env artifact mods current_src) (expr_type e) v /\
       constant_result_shape pv) /\
  (!mods imms es vs cx am sc artifact current_src mode checker_layouts checker_addr.
     constant_values mods imms es = SOME vs /\
     check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist) checker_addr mods = SOME artifact /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     constant_machine_immutables am cx.txn.target = imms /\
     deployment_constant_cells_typed (type_env_all_modules mods)
       cx.txn.target mods am /\
     well_typed_exprs (artifact_env artifact mods current_src) es /\
     EVERY (constant_expr mods) es ==>
     eval_exprs cx es (initial_state am sc) = (INL vs,initial_state am sc) /\
     LIST_REL (\e v. value_runtime_typed (artifact_env artifact mods current_src)
       (expr_type e) v) es vs /\
     LIST_REL (\e v. ?pv.
       eval_expr cx e (initial_state am sc) = (INL pv,initial_state am sc) /\
       read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
       constant_result_shape pv) es vs)
Proof
  ho_match_mp_tac constant_value_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`TopLevelName`] >- (
    Cases_on `ALOOKUP am.immutables cx.txn.target`
    >- gvs[constant_machine_immutables_def, constant_value_def,
           get_source_immutables_def, AllCaseEqs()] >>
    gvs[constant_machine_immutables_def] >> simp[expr_type_def] >>
    irule checked_constant_name_result >> metis_tac[])
  >~ [`Literal`] >- (
    gvs[constant_value_def, well_typed_expr_def] >>
    qexists `Value (evaluate_literal l)` >>
    simp[Once evaluate_def, return_def, read_result_def,
         eval_result_typed_def, value_runtime_typed_def, constant_result_shape_def] >>
    gvs[expr_type_def, well_formed_type_def, IS_SOME_EXISTS] >>
    metis_tac[well_typed_literal_sound])
  >~ [`StructLit`] >- (
    gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
    `well_typed_exprs (artifact_env artifact mods current_src) (MAP SND kes)` by
      (irule constant_named_exprs_typed >> gvs[well_typed_expr_def]) >>
    `EVERY (constant_expr mods) (MAP SND kes)` by fs[EVERY_MEM] >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >>
    disch_then (qspec_then `sc` strip_assume_tac) >>
    `value_runtime_typed (artifact_env artifact mods current_src) v4
       (StructV (ZIP (MAP FST kes,vs)))` by
      (irule constant_struct_value_typed >> metis_tac[]) >>
    qexists `Value (StructV (ZIP (MAP FST kes,vs)))` >>
    PairCases_on `v5` >>
    simp[Once evaluate_def, bind_def, return_def, read_result_def,
         expr_type_def, eval_result_typed_def, constant_result_shape_def] >>
    gvs[value_runtime_typed_def])
  >~ [`Subscript`] >- (
    `well_typed_expr (artifact_env artifact mods current_src) e` by
      (irule constant_subscript_base_well_typed >> metis_tac[constant_expr_def]) >>
    `subscript_type_ok (expr_type e) e' v6` by
      metis_tac[constant_subscript_type_ok] >>
    gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
    `well_typed_expr (artifact_env artifact mods current_src) e'` by
      gvs[Once well_typed_expr_def] >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> disch_then (qspec_then `sc` strip_assume_tac) >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> disch_then (qspec_then `sc` strip_assume_tac) >>
    `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
    `value_has_type arr_tv v1` by gvs[value_runtime_typed_def, artifact_env_def] >>
    `vyperTypeExprResult$subscript_index_matches (expr_type e) e' v2` by
      metis_tac[constant_subscript_index_matches] >>
    `evaluate_type (artifact_env artifact mods current_src).type_defs
       (expr_type e) = SOME arr_tv` by simp[artifact_env_def] >>
    drule_all constant_subscript_selected_typed >> strip_tac >>
    `(artifact_env artifact mods current_src).type_defs = get_tenv cx` by
      simp[artifact_env_def] >>
    drule_all constant_result_selection >> strip_tac >>
    qexists `out` >>
    simp[Once evaluate_def, bind_def, expr_type_def, value_runtime_typed_def] >>
    metis_tac[])
  >~ [`Attribute`] >- (
    gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
    `well_typed_expr (artifact_env artifact mods current_src) e /\
     attribute_type (artifact_env artifact mods current_src).type_defs
       (expr_type e) id = SOME v7` by
      gvs[Once well_typed_expr_def, attribute_type_ok_def] >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> disch_then (qspec_then `sc` strip_assume_tac) >>
    gvs[value_runtime_typed_def] >>
    `evaluate_subscripts tv v' [AttrSubscript id] = INL v` by
      (Cases_on `v'` >> gvs[vyperValueOperationTheory.evaluate_attribute_def,
                              evaluate_subscripts_def, AllCaseEqs()]) >>
    drule_all constant_attribute_selected_typed >> strip_tac >>
    `(artifact_env artifact mods current_src).type_defs = get_tenv cx` by
      simp[artifact_env_def, get_tenv_def] >>
    drule_all constant_result_selection >> strip_tac >>
    qexists `out` >>
    simp[Once evaluate_def, bind_def, expr_type_def, value_runtime_typed_def] >>
    metis_tac[])
  >~ [`Builtin`] >- (
    `well_typed_exprs (artifact_env artifact mods current_src) es /\
     well_typed_builtin_app ty bt (MAP expr_type es) /\
     well_formed_type (artifact_env artifact mods current_src).type_defs ty` by
      gvs[Once well_typed_expr_def] >>
    gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
    `EVERY (constant_expr mods) es` by fs[EVERY_MEM] >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> disch_then (qspec_then `sc` strip_assume_tac) >>
    `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
    gvs[] >>
    (all_tac >>~- ([`constant_length _ = SOME _`],
      drule_all constant_result_length >> strip_tac >>
      gvs[value_runtime_typed_def] >>
      `evaluate_type (artifact_env artifact mods current_src).type_defs ty = SOME (BaseTV (UintT 256))` by
        (gvs[well_typed_builtin_app_def] >> simp[evaluate_type_def]) >>
      `value_has_type (BaseTV (UintT 256)) (IntV (&n))` by
        (irule constant_len_success_typed >> metis_tac[]) >>
      qexists `Value (IntV (&n))` >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, expr_type_def,
           eval_result_typed_def, read_result_def, constant_result_shape_def,
           value_runtime_typed_def])) >>
    (all_tac >>~- ([`evaluate_membership _ _ _ _ = INL _`],
      gvs[value_runtime_typed_def] >>
      `!t. evaluate_type (artifact_env artifact mods current_src).type_defs t =
           evaluate_type (type_env_all_modules mods) t` by simp[artifact_env_def] >>
      gvs[] >>
      drule typed_membership_success >>
      simp[] >> disch_then drule_all >> strip_tac >> gvs[] >>
      qexists `Value (BoolV b)` >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, lift_sum_def,
           lift_option_type_def, lift_option_def, expr_type_def,
           eval_result_typed_def, read_result_def, constant_result_shape_def,
           value_runtime_typed_def, artifact_env_def, evaluate_type_def,
           value_has_type_def])) >>
    `exprs_runtime_typed (artifact_env artifact mods current_src) es vs` by
      metis_tac[constant_values_runtime_types] >>
    gvs[exprs_runtime_typed_def] >>
    `?tv. evaluate_type (artifact_env artifact mods current_src).type_defs ty = SOME tv` by
      gvs[well_formed_type_def, IS_SOME_EXISTS] >>
    `evaluate_builtin cx (initial_state am sc).accounts ty bt (MAP expr_type es) vs = INL v` by
      metis_tac[evaluate_builtin_constant_context] >>
    `value_has_type tv v` by
      (drule_at (Pat `evaluate_builtin cx _ _ _ _ _ = _`)
         constant_builtin_success_typed >>
       disch_then (qspecl_then [`tvs`,`tv`,`mods`] mp_tac) >>
       simp[artifact_env_def, MAP_MAP_o] >> impl_tac
       >- (gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP, artifact_env_def] >> metis_tac[]) >>
       simp[]) >>
    qexists `Value v` >>
    simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
         lift_sum_def, get_accounts_def, return_def, expr_type_def, eval_result_typed_def,
         read_result_def, value_runtime_typed_def, constant_result_shape_def] >>
    metis_tac[])
  >~ [`TypeBuiltin`] >- (
    `well_typed_exprs (artifact_env artifact mods current_src) es /\
     well_formed_type (artifact_env artifact mods current_src).type_defs v8 /\
     type_builtin_result_ok (artifact_env artifact mods current_src).type_defs
       tb v8 typ (MAP expr_type es) /\
     well_typed_type_builtin_args tb typ (MAP expr_type es)` by
      gvs[Once well_typed_expr_def] >>
    gvs[constant_value_def, constant_expr_def, AllCaseEqs()] >>
    `EVERY (constant_expr mods) es` by fs[EVERY_MEM] >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> disch_then (qspec_then `sc` strip_assume_tac) >>
    `get_tenv cx = type_env_all_modules mods` by metis_tac[get_tenv_sources] >>
    `evaluate_type_builtin cx tb typ (MAP expr_type es) vs = INL v` by
      metis_tac[evaluate_type_builtin_constant_context] >>
    `?tv. evaluate_type (artifact_env artifact mods current_src).type_defs v8 = SOME tv` by
      gvs[well_formed_type_def, IS_SOME_EXISTS] >>
    `value_has_type tv v` by
      (drule_at (Pat `evaluate_type_builtin _ _ _ _ _ = _`)
         constant_type_builtin_success_typed >>
       disch_then (qspecl_then [`v8`,`tv`] mp_tac) >>
       gvs[artifact_env_def, get_tenv_constant_context]) >>
    qexists `Value v` >>
    simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
         lift_sum_def, return_def, expr_type_def, eval_result_typed_def,
         read_result_def, value_runtime_typed_def, constant_result_shape_def] >>
    metis_tac[])
  >~ [`constant_values _ _ []`] >- gvs[constant_value_def, Once evaluate_def, return_def]
  >~ [`LIST_REL _ [] _`] >- gvs[constant_value_def]
  >>~- ([`constant_values _ _ (e::es)`],
    gvs[constant_value_def, well_typed_expr_def, AllCaseEqs()] >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> disch_then (qspec_then `sc` strip_assume_tac) >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> disch_then (qspec_then `sc` strip_assume_tac) >>
    simp[Once evaluate_def, bind_def, return_def] >> metis_tac[]) >>
  gvs[constant_value_def]
QED
Theorem constant_value_eval_expr_checked:
  (!mods imms e v cx am sc artifact current_src mode checker_layouts checker_addr.
     constant_value mods imms e = SOME v /\
     check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist)
       checker_addr mods = SOME artifact /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     constant_machine_immutables am cx.txn.target = imms /\
     deployment_constant_cells_typed (type_env_all_modules mods)
       cx.txn.target mods am /\
     well_typed_expr (artifact_env artifact mods current_src) e /\
     constant_expr mods e ==>
     ?pv. eval_expr cx e (initial_state am sc) = (INL pv,initial_state am sc) /\
       eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
         pv (Type (expr_type e)) /\
       read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
       value_runtime_typed (artifact_env artifact mods current_src) (expr_type e) v) /\
  (!mods imms es vs cx am sc artifact current_src mode checker_layouts checker_addr.
     constant_values mods imms es = SOME vs /\
     check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist)
       checker_addr mods = SOME artifact /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     constant_machine_immutables am cx.txn.target = imms /\
     deployment_constant_cells_typed (type_env_all_modules mods)
       cx.txn.target mods am /\
     well_typed_exprs (artifact_env artifact mods current_src) es /\
     EVERY (constant_expr mods) es ==>
     eval_exprs cx es (initial_state am sc) = (INL vs,initial_state am sc) /\
     LIST_REL (\e v. value_runtime_typed (artifact_env artifact mods current_src)
       (expr_type e) v) es vs)
Proof
  conj_tac >> rpt gen_tac >> strip_tac
  >- (drule_all (cj 1 constant_value_eval_expr_shape) >> metis_tac[]) >>
  drule_all (cj 2 constant_value_eval_expr_shape) >> simp[]
QED


Theorem constant_value_eval_expr:
  (!mods imms e v cx am sc artifact current_src.
     constant_value mods imms e = SOME v /\
     check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     constant_machine_immutables am cx.txn.target = imms /\
     deployment_constant_cells_typed (type_env_all_modules mods)
       cx.txn.target mods am /\
     well_typed_expr (artifact_env artifact mods current_src) e /\
     constant_expr mods e ==>
     ?pv. eval_expr cx e (initial_state am sc) = (INL pv,initial_state am sc) /\
       eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
         pv (Type (expr_type e)) /\
       read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) /\
       value_runtime_typed (artifact_env artifact mods current_src) (expr_type e) v) /\
  (!mods imms es vs cx am sc artifact current_src.
     constant_values mods imms es = SOME vs /\
     check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     constant_machine_immutables am cx.txn.target = imms /\
     deployment_constant_cells_typed (type_env_all_modules mods)
       cx.txn.target mods am /\
     well_typed_exprs (artifact_env artifact mods current_src) es /\
     EVERY (constant_expr mods) es ==>
     eval_exprs cx es (initial_state am sc) = (INL vs,initial_state am sc) /\
     LIST_REL (\e v. value_runtime_typed (artifact_env artifact mods current_src)
       (expr_type e) v) es vs)
Proof
  conj_tac >> rpt gen_tac >> strip_tac
  >- (drule_all (cj 1 constant_value_eval_expr_shape) >> metis_tac[]) >>
  drule_all (cj 2 constant_value_eval_expr_shape) >> simp[]
QED

(* ===== Fold soundness ===== *)

Theorem merge_constants_immutables:
  ALOOKUP am.immutables addr = SOME imms ==>
  ALOOKUP (merge_constants addr src cenv am).immutables addr =
    SOME (merge_constant_imms src cenv imms)
Proof
  simp[merge_constants_def, merge_constant_imms_def]
QED

Theorem constant_fold_resolved_typed[local]:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) e /\ constant_expr mods e /\
  constant_value mods (constant_machine_immutables am cx.txn.target) e = SOME v /\
  eval_expr cx e (initial_state am sc) = (INL pv,initial_state am sc) ==>
  eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
    pv (Type (expr_type e))
Proof
  strip_tac >> drule (cj 1 constant_value_eval_expr) >>
  disch_then (qspecl_then [`cx`,`am`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`sc`,`current_src`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem constant_exprs_MEM_typed[local]:
  !es. well_typed_exprs env es ==> !e. MEM e es ==> well_typed_expr env e
Proof
  Induct >> simp[well_typed_expr_def] >> metis_tac[]
QED

Theorem constant_eval_exprs_fold_lift[local]:
  !es vs st'.
    (!e pv next. MEM e es /\ eval_expr cx e st = (INL pv,next) ==>
       next = st /\
       !v. read_result cx pv st = (INL v,st) ==>
         constant_value mods imms e = SOME v) /\
    eval_exprs cx es st = (INL vs,st') ==>
    st' = st /\ constant_values mods imms es = SOME vs
Proof
  Induct_on `es` >> rpt gen_tac >> strip_tac
  >- gvs[Once evaluate_def, return_def, constant_value_def] >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >> strip_tac >>
  gvs[sum_CASE_rator, AllCaseEqs()] >>
  drule read_result_state >>
  disch_then SUBST_ALL_TAC >>
  `constant_value mods imms h = SOME v''` by metis_tac[] >>
  rename1 `eval_exprs cx es st = (INL tailvals,tailstate)` >>
  `tailstate = st /\ constant_values mods imms es = SOME tailvals` by metis_tac[] >>
  qpat_x_assum `!e pv next. _` kall_tac >>
  gvs[return_def, constant_value_def]
QED

Theorem constant_eval_expr_fold_agreement[local]:
  !mods e. constant_expr mods e ==>
  !cx am sc artifact current_src pv st'.
    check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    deployment_constant_cells_typed (type_env_all_modules mods)
      cx.txn.target mods am /\
    well_typed_expr (artifact_env artifact mods current_src) e /\
    eval_expr cx e (initial_state am sc) = (INL pv,st') ==>
    st' = initial_state am sc /\ constant_result_shape pv /\
    !v. read_result cx pv st' = (INL v,st') ==>
      constant_value mods (constant_machine_immutables am cx.txn.target) e = SOME v
Proof
  recInduct constant_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[constant_expr_def]
  >~ [`TopLevelName`] >- suspend "name"
  >~ [`Literal`] >- suspend "literal"
  >~ [`StructLit`] >- suspend "struct"
  >~ [`Attribute`] >- suspend "attribute"
  >~ [`Subscript`] >- suspend "subscript"
  >~ [`Builtin`] >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume constant_eval_expr_fold_agreement[name]:

    strip_tac >> rpt gen_tac >> strip_tac >>
    fs[declared_constant_def] >>
    `contract_namespaces_ok F mods` by
      metis_tac[check_contract_runtime_namespaces] >>
    `ALOOKUP mods src = SOME tls` by
      (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[contract_namespaces_ok_def]) >>
    `find_var_decl_by_name id tls = NONE` by
      (irule find_var_decl_by_name_NONE_Constant >>
       metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys]) >>
    gvs[Once evaluate_def, lookup_global_def, get_module_code_def,
        get_tenv_def, get_immutables_def, get_address_immutables_def,
        bind_def, lift_option_type_def, return_def, raise_def,
        option_CASE_rator, AllCaseEqs()] >>
    simp[constant_result_shape_def] >> rpt strip_tac >>
    drule constant_immutable_read_inv >> strip_tac >>
    gvs[initial_state_def, evaluate_subscripts_def,
        constant_machine_immutables_def, constant_value_def]
QED

Resume constant_eval_expr_fold_agreement[literal]:
    rpt gen_tac >> strip_tac >>
    gvs[Once evaluate_def, return_def, constant_result_shape_def,
        read_result_def, constant_value_def]
QED

Resume constant_eval_expr_fold_agreement[struct]:
    strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    `well_typed_exprs (artifact_env artifact mods current_src) (MAP SND kes)` by
      (irule constant_named_exprs_typed >> gvs[well_typed_expr_def]) >>
    `!e pv next. MEM e (MAP SND kes) /\
       eval_expr cx e (initial_state am sc) = (INL pv,next) ==>
       next = initial_state am sc /\
       !v. read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) ==>
         constant_value mods (constant_machine_immutables am cx.txn.target) e = SOME v` by
      (fs[EVERY_MEM] >> metis_tac[constant_exprs_MEM_typed]) >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    PairCases_on `v4` >>
    simp[Once evaluate_def, bind_def, return_def] >> strip_tac >>
    gvs[sum_CASE_rator, AllCaseEqs()] >>
    drule_all constant_eval_exprs_fold_lift >> strip_tac >>
    gvs[return_def, constant_result_shape_def, read_result_def, constant_value_def]
QED

Resume constant_eval_expr_fold_agreement[attribute]:
    strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    `well_typed_expr (artifact_env artifact mods current_src) e` by
      gvs[Once well_typed_expr_def] >>
    qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def] >> strip_tac >>
    gvs[sum_CASE_rator, AllCaseEqs()] >>
    first_x_assum drule_all >> strip_tac >>
    drule_all constant_result_selection_base >> strip_tac >> gvs[] >>
    `constant_value mods (constant_machine_immutables am cx.txn.target) e = SOME v` by
      metis_tac[] >>
    `eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
       res (Type (expr_type e))` by
      (irule constant_fold_resolved_typed >> metis_tac[]) >>
    `?tv. evaluate_type (artifact_env artifact mods current_src).type_defs
       (expr_type e) = SOME tv` by gvs[eval_result_typed_def] >>
    `(artifact_env artifact mods current_src).type_defs = get_tenv cx` by
      simp[artifact_env_def, get_tenv_def] >>
    simp[] >> rpt strip_tac >>
    drule_all constant_result_selection_inv >> strip_tac >>
    gvs[constant_value_def] >> Cases_on `v` >>
    gvs[evaluate_subscripts_def, vyperValueOperationTheory.evaluate_attribute_def,
        AllCaseEqs()]
QED

Resume constant_eval_expr_fold_agreement[subscript]:
    strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    `well_typed_expr (artifact_env artifact mods current_src) e1` by
      (drule_all constant_subscript_base_well_typed >> simp[]) >>
    `well_typed_expr (artifact_env artifact mods current_src) e2` by
      gvs[Once well_typed_expr_def] >>
    qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def] >> strip_tac >>
    gvs[sum_CASE_rator, AllCaseEqs()] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    first_x_assum drule_all >> strip_tac >> gvs[] >>
    drule read_result_state >> disch_then SUBST_ALL_TAC >>
    drule_all constant_result_selection_base >> strip_tac >> gvs[] >>
    `eval_result_typed (artifact_env artifact mods current_src,cx,initial_state am sc)
       res (Type (expr_type e1))` by
      (irule constant_fold_resolved_typed >> metis_tac[]) >>
    `?tv. evaluate_type (artifact_env artifact mods current_src).type_defs
       (expr_type e1) = SOME tv` by gvs[eval_result_typed_def] >>
    `(artifact_env artifact mods current_src).type_defs = get_tenv cx` by
      simp[artifact_env_def, get_tenv_def] >>
    rpt strip_tac >> drule_all constant_result_selection_inv >> strip_tac >>
    gvs[constant_value_def, evaluate_subscripts_def, get_tenv_def, AllCaseEqs()]
QED

Resume constant_eval_expr_fold_agreement[builtin]:
    strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    `well_typed_exprs (artifact_env artifact mods current_src) es` by
      gvs[Once well_typed_expr_def] >>
    Cases_on `bt = Len`
    >- (gvs[] >>
      qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def] >> strip_tac >>
      gvs[sum_CASE_rator, AllCaseEqs()] >>
      `?e. es = [e]` by
        (Cases_on `es` >> gvs[builtin_args_length_ok_def] >>
         Cases_on `t` >> gvs[]) >> gvs[well_typed_expr_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule_all constant_result_length_inv >> strip_tac >> gvs[] >>
      gvs[constant_result_shape_def, read_result_def, return_def, constant_value_def]) >>
    `!e pv next. MEM e es /\
       eval_expr cx e (initial_state am sc) = (INL pv,next) ==>
       next = initial_state am sc /\
       !v. read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) ==>
         constant_value mods (constant_machine_immutables am cx.txn.target) e = SOME v` by
      (fs[EVERY_MEM] >> metis_tac[constant_exprs_MEM_typed]) >>
    Cases_on `bt = Bop In \/ bt = Bop NotIn`
    >- (qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
        simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
             assert_def, lift_sum_def, lift_option_type_def, lift_option_def,
             return_def, raise_def] >> strip_tac >>
        gvs[sum_CASE_rator, AllCaseEqs()] >>
        drule_all constant_eval_exprs_fold_lift >> strip_tac >>
        gvs[return_def, raise_def, constant_result_shape_def, read_result_def] >>
        `get_tenv cx = type_env_all_modules mods` by simp[get_tenv_def] >>
        gvs[LENGTH_EQ_NUM_compute, constant_value_def] >>
        Cases_on `evaluate_type (type_env_all_modules mods) (expr_type (EL 1 es))` >>
        gvs[return_def, raise_def]) >>
    qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
         lift_sum_def, get_accounts_def, return_def] >> strip_tac >>
    gvs[sum_CASE_rator, AllCaseEqs()] >>
    drule_all constant_eval_exprs_fold_lift >> strip_tac >>
    gvs[return_def, raise_def, constant_result_shape_def, read_result_def] >>
    `get_tenv cx = type_env_all_modules mods` by simp[get_tenv_def] >>
    `evaluate_builtin (constant_context mods) empty_accounts v8 bt (MAP expr_type es) vs = INL v''` by
      metis_tac[evaluate_builtin_constant_context] >>
    gvs[constant_value_def]
QED

Resume constant_eval_expr_fold_agreement[type_builtin]:
  strip_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `well_typed_exprs (artifact_env artifact mods current_src) es` by
    gvs[Once well_typed_expr_def] >>
  `!e pv next. MEM e es /\
     eval_expr cx e (initial_state am sc) = (INL pv,next) ==>
     next = initial_state am sc /\
     !v. read_result cx pv (initial_state am sc) = (INL v,initial_state am sc) ==>
       constant_value mods (constant_machine_immutables am cx.txn.target) e = SOME v` by
    (fs[EVERY_MEM] >> metis_tac[constant_exprs_MEM_typed]) >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       lift_sum_def, return_def] >> strip_tac >>
  gvs[sum_CASE_rator, AllCaseEqs()] >>
  drule_all constant_eval_exprs_fold_lift >> strip_tac >>
  gvs[return_def, raise_def, constant_result_shape_def, read_result_def] >>
  `get_tenv cx = type_env_all_modules mods` by simp[get_tenv_def] >>
  `evaluate_type_builtin (constant_context mods) tb v10 (MAP expr_type es) vs = INL v''` by
    metis_tac[evaluate_type_builtin_constant_context] >>
  gvs[constant_value_def]
QED

Finalise constant_eval_expr_fold_agreement

Theorem constant_eval_expr_read_fold_agreement:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) e /\ constant_expr mods e /\
  (do pv <- eval_expr cx e; read_result cx pv od) (initial_state am sc) = (INL v,st') ==>
  st' = initial_state am sc /\
  constant_value mods (constant_machine_immutables am cx.txn.target) e = SOME v
Proof
  strip_tac >> gvs[bind_def, sum_CASE_rator, AllCaseEqs()] >>
  drule_all constant_eval_expr_fold_agreement >> strip_tac >> gvs[] >>
  drule read_result_state >> strip_tac >> gvs[]
QED

Theorem constant_eval_exprs_fold_agreement:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_exprs (artifact_env artifact mods current_src) es /\
  EVERY (constant_expr mods) es /\
  eval_exprs cx es (initial_state am sc) = (INL vs,st') ==>
  st' = initial_state am sc /\
  constant_values mods (constant_machine_immutables am cx.txn.target) es = SOME vs
Proof
  strip_tac >> irule constant_eval_exprs_fold_lift >> qexists `cx` >>
  conj_tac >- (rpt strip_tac >>
    `constant_expr mods e /\
     well_typed_expr (artifact_env artifact mods current_src) e` by
      metis_tac[EVERY_MEM, constant_exprs_MEM_typed] >>
    drule_all constant_eval_expr_fold_agreement >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem constant_eval_expr_read_typed:
  check_contract F cx.layouts cx.txn.target mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
  well_typed_expr (artifact_env artifact mods current_src) e /\ constant_expr mods e /\
  (do pv <- eval_expr cx e; read_result cx pv od) (initial_state am sc) = (INL v,st') ==>
  value_runtime_typed (artifact_env artifact mods current_src) (expr_type e) v
Proof
  strip_tac >> drule_all constant_eval_expr_read_fold_agreement >> strip_tac >>
  drule (cj 1 constant_value_eval_expr) >>
  disch_then (qspecl_then [`cx`,`am`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`sc`,`current_src`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem constants_fold_module_constants_env:
  !mods imms src ts acc.
  !cenv cx am full artifact mode layouts addr.
    constants_fold_module mods imms src ts acc = SOME cenv /\
    check_contract mode (layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist)
      addr mods = SOME artifact /\
    ALOOKUP mods src = SOME full /\ EVERY (\tl. MEM tl full) ts /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ALOOKUP am.immutables cx.txn.target = SOME imms /\
    deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am /\
    constant_fmap_declared_typed (type_env_all_modules mods) full acc ==>
    constants_env cx am cx.txn.target src ts acc = SOME cenv /\
    constant_fmap_declared_typed (type_env_all_modules mods) full cenv
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rw[constants_fold_module_def, constants_env_def] >>
  gvs[AllCaseEqs()]
  >>~- ([`constant_value mods (merge_constant_imms src acc imms) e = SOME v`],
    drule_all checked_constant_decl_typed >> strip_tac >>
    `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
    `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods
       (merge_constants cx.txn.target src acc am)` by
      (irule merge_constants_preserves_constant_cells_typed >> metis_tac[]) >>
    `ALOOKUP (merge_constants cx.txn.target src acc am).immutables cx.txn.target =
       SOME (merge_constant_imms src acc imms)` by simp[merge_constants_immutables] >>
    `constant_machine_immutables
       (merge_constants cx.txn.target src acc am) cx.txn.target =
       merge_constant_imms src acc imms` by
      simp[constant_machine_immutables_def] >>
    drule_all (cj 1 constant_value_eval_expr_checked) >>
    disch_then (qspec_then `[FEMPTY]` strip_assume_tac) >>
    `value_has_type tv v` by gvs[value_runtime_typed_def, artifact_env_def] >>
    `constant_fmap_declared_typed (type_env_all_modules mods) full
       (acc |+ (id,(tv,v)))` by
      (irule constant_fmap_declared_typed_update >> metis_tac[]) >>
    first_x_assum (qspecl_then [`cx`,`am`] mp_tac) >>
    simp[] >> disch_then drule_all >> strip_tac >>
    simp[get_tenv_def, bind_def]) >>
  metis_tac[]
QED

(* TOP-LEVEL: when the checker's fold succeeds, so does deployment's, leaving
   the same immutables for the contract. *)
Theorem constants_fold_evaluate_module_constants:
  !rest imms am imms' cx artifact mode layouts addr.
    constants_fold mods imms rest = SOME imms' /\
    check_contract mode (layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist)
      addr mods = SOME artifact /\
    EVERY (\m. MEM m mods) rest /\
    ALOOKUP cx.sources cx.txn.target = SOME mods /\
    ALOOKUP am.immutables cx.txn.target = SOME imms /\
    deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am ==>
    ?am_c.
      evaluate_module_constants cx am cx.txn.target rest = SOME am_c /\
      ALOOKUP am_c.immutables cx.txn.target = SOME imms' /\
      deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am_c
Proof
  Induct >- simp[constants_fold_def, evaluate_module_constants_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  rw[constants_fold_def, evaluate_module_constants_def] >> gvs[AllCaseEqs()] >>
  `contract_namespaces_ok F mods` by metis_tac[check_contract_runtime_namespaces] >>
  `ALOOKUP mods h0 = SOME h1` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[contract_namespaces_ok_def]) >>
  `constants_env (set_current_module cx h0) am cx.txn.target h0 h1 FEMPTY = SOME cenv /\
   constant_fmap_declared_typed (type_env_all_modules mods) h1 cenv` by
    (drule constants_fold_module_constants_env >>
     disch_then (qspec_then `set_current_module cx h0` mp_tac) >>
     simp[set_current_module_def, EVERY_MEM] >> disch_then drule_all >> simp[]) >>
  `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods
     (merge_constants cx.txn.target h0 cenv am)` by
    (irule merge_constants_preserves_constant_cells_typed >> metis_tac[]) >>
  `ALOOKUP (merge_constants cx.txn.target h0 cenv am).immutables cx.txn.target =
     SOME (merge_constant_imms h0 cenv imms)` by simp[merge_constants_immutables] >>
  simp[] >> first_x_assum drule_all >> simp[]
QED

(* TOP-LEVEL: for a checked contract the deployment constants fold succeeds
   from the immutables load_contract installs, in any context whose contract
   code is mods. *)
Theorem check_contract_evaluate_all_constants:
  check_contract in_deploy layouts addr mods = SOME art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP am.immutables cx.txn.target = SOME imms ==>
  IS_SOME (evaluate_all_constants cx am cx.txn.target mods)
Proof
  strip_tac >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def] >> rw[]) >>
  gvs[contract_constants_ok_def, IS_SOME_EXISTS, evaluate_all_constants_def] >>
  `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am` by
    (rw[deployment_constant_cells_typed_def] >>
     drule_all checked_initial_immutables_constant_absent >> gvs[]) >>
  drule_at (Pat `check_contract _ _ _ _ = _`) constants_fold_evaluate_module_constants >>
  disch_then (qspec_then `constants_order mods` mp_tac) >>
  simp[EVERY_MEM, MEM_constants_order] >> disch_then drule_all >> metis_tac[]
QED

Theorem ALL_DISTINCT_contract_keys_constants_order[local]:
  ALL_DISTINCT (contract_keys f (constants_order mods)) <=>
  ALL_DISTINCT (contract_keys f mods)
Proof
  irule ALL_DISTINCT_PERM >> simp[contract_keys_def] >>
  irule PERM_FLAT >> irule PERM_MAP >> simp[PERM_constants_order]
QED

Theorem contract_namespaces_ok_constants_order:
  contract_namespaces_ok b (constants_order mods) <=> contract_namespaces_ok b mods
Proof
  `ALL_DISTINCT (MAP FST (constants_order mods)) <=> ALL_DISTINCT (MAP FST mods)` by (
    irule ALL_DISTINCT_PERM >> irule PERM_MAP >> simp[PERM_constants_order]) >>
  simp[contract_namespaces_ok_def, ALL_DISTINCT_contract_keys_constants_order]
QED
