(*
 * Checked-contract type-soundness bridge properties.
 *
 * The definitions in vyperTypeContract build a contract_type_artifact from a
 * module set and check that declarations/bodies satisfy the static rules.  This
 * theory proves that successful checking supplies the proof-facing consistency
 * predicates used by the type-soundness theorems.
 *)

Theory vyperTypeContractGetter
Ancestors
  list rich_list arithmetic finite_map alist option pair patricia_casts
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeInitialState vyperPureExpr vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperScopePreservation vyperStatePreservation
  vyperTypeContractStaticMaps
Libs
  wordsLib

val _ = Parse.hide "body";

Definition is_public_getter_decl_def:
  is_public_getter_decl fn (VariableDecl Public mut id typ init) = (id = fn) /\
  is_public_getter_decl fn (HashMapDecl Public is_transient id kt vt init) = (id = fn) /\
  is_public_getter_decl _ _ = F
End

Definition external_getter_tuple_def:
  external_getter_tuple src (VariableDecl Public mut id typ init) =
    (if ~is_ArrayT typ then
       SOME (View,F,[],[],typ,[Return (SOME (TopLevelName NoneT (src,id)))])
     else
       SOME (getter (TopLevelName NoneT (src,id)) (BaseT (UintT 256)) (Type (ArrayT_type typ)))) /\
  external_getter_tuple src (HashMapDecl Public is_transient id kt vt init) =
    SOME (getter (TopLevelName NoneT (src,id)) kt vt) /\
  external_getter_tuple _ _ = NONE
End

Theorem lookup_function_External_cases[local]:
  lookup_function src fn External ts = SOME (mut,nr,args,dflts,ret,body) ==>
  (?raw. MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts) \/
  (?decl. MEM decl ts /\ is_public_getter_decl fn decl /\
          external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body))
Proof
  Induct_on `ts` >- rw[lookup_function_def] >>
  gen_tac >> Cases_on `h` >>
  rw[lookup_function_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  TRY (Cases_on `v`) >>
  gvs[AllCaseEqs(), lookup_function_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  TRY (disj1_tac >> qexists `b0` >> simp[] >> NO_TAC) >>
  TRY (disj1_tac >> qexists `raw` >> simp[] >> NO_TAC) >>
  TRY (disj1_tac >> goal_assum (drule_at Any) >> simp[] >> NO_TAC) >>
  TRY (disj2_tac >> qexists `VariableDecl Public v0 fn ret o'` >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  TRY (disj2_tac >> qexists `VariableDecl Public v0 fn t o'` >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  TRY (disj2_tac >> qexists `HashMapDecl Public b fn t v0 o'` >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  TRY (disj2_tac >> goal_assum (drule_at Any) >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  metis_tac[]
QED

Theorem lookup_exported_function_checked_cases_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  src = find_function_module am tx.target tx.function_name /\
  get_module_code cx src = SOME ts /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) ==>
  (?raw.
     MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts) \/
  (?decl.
     MEM decl ts /\
     is_public_getter_decl tx.function_name decl /\
     external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body))
Proof
  rpt strip_tac >>
  gvs[find_function_module_def, initial_evaluation_context_def] >>
  gvs[lookup_exported_function_def, get_self_code_def, AllCaseEqs()] >>
  drule lookup_function_External_cases >>
  simp[]
QED


Theorem scalar_raw_public_getter_body_typing_annotation_contradiction[local]:
  typ <> NoneT /\
  FLOOKUP env.toplevel_vtypes (src,string_to_num fn) = SOME (Type typ) ==>
  type_stmts env typ [Return (SOME (TopLevelName NoneT (src,fn)))] = NONE
Proof
  rw[type_stmt_def, well_typed_expr_def]
QED

Theorem raw_getter_index_name_annotation_contradiction[local]:
  kt <> NoneT /\
  FLOOKUP env.var_types (string_to_num vn) = SOME kt ==>
  ~well_typed_expr env (Name NoneT vn)
Proof
  rw[well_typed_expr_def]
QED

Theorem checked_scalar_public_getter_body_typing_package_contradiction[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  ~is_ArrayT typ ==>
  ~(?env_after.
      type_stmts (artifact_env art mods src) typ
        [Return (SOME (TopLevelName NoneT (src,fn)))] = SOME env_after)
Proof
  rw[] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def, get_module_code_def,
         initial_evaluation_context_def] >>
     metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `typ <> NoneT` by
    (Cases_on `mut` >> gvs[check_toplevel_decl_def] >>
     metis_tac[assignable_type_not_NoneT]) >>
  `type_stmts (artifact_env art mods src) typ
     [Return (SOME (TopLevelName NoneT (src,fn)))] = NONE` by
    (irule scalar_raw_public_getter_body_typing_annotation_contradiction >>
     simp[artifact_env_def]) >>
  gvs[]
QED
(* ===== Top-level checked call_external no-TypeError theorem ===== *)

Theorem checked_scalar_public_getter_eval_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
      imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem checked_scalar_public_getter_eval_no_type_error_materialisable:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule checked_scalar_public_getter_eval_no_type_error >> metis_tac[]) >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem checked_scalar_public_getter_eval_no_type_error_materialisable_post_prefix:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
      simp[get_module_code_def, initial_evaluation_context_def] >>
    `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
      (`toplevel_vtypes_complete art.cta_toplevel_vtypes
          (initial_evaluation_context am.sources am.layouts tx src)` by
         (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
       gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
    `check_toplevel_decl am.layouts tx.target mods art src
       (VariableDecl Public mut fn typ init)` by
      metis_tac[check_contract_toplevel_decl_MEM] >>
    `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
      (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
       gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
         return_def, raise_def, initial_evaluation_context_def] >>
    Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                          well_formed_type_def]
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts =
           SOME (StorageVarDecl T typ,fn)` by
          metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                    contract_namespaces_ok_module_toplevel_vtype_keys,
                    ALOOKUP_MEM, check_contract_def] >>
        gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
            get_tenv_def, initial_evaluation_context_def] >>
        drule assignable_type_well_formed >> simp[well_formed_type_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
        gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
        imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
        gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
    `find_var_decl_by_num (string_to_num fn) ts =
       SOME (StorageVarDecl F typ,fn)` by
      metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
                contract_namespaces_ok_module_toplevel_vtype_keys,
                ALOOKUP_MEM, check_contract_def] >>
    gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
        get_tenv_def, initial_evaluation_context_def] >>
    drule assignable_type_well_formed >> simp[well_formed_type_def] >>
    strip_tac >> gvs[IS_SOME_EXISTS] >>
    Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
    gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
    imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
    gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem bind_arguments_scope_covers_params_getter:
  !tenv params vs sc id typ.
    bind_arguments tenv params vs = SOME sc /\ MEM (id,typ) params /\
    (!id' typ'. MEM (id',typ') params /\ string_to_num id' = string_to_num id ==> typ' = typ) ==>
    ?entry. FLOOKUP sc (string_to_num id) = SOME entry /\
            evaluate_type tenv typ = SOME entry.type /\ entry.assignable
Proof
  Induct_on `params` >> simp[Once bind_arguments_def] >>
  Cases >> simp[Once bind_arguments_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac
  >- (qexists_tac `<|assignable := T; type := tv; value := v'|>` >>
      qpat_x_assum `id = q` SUBST_ALL_TAC >>
      qpat_x_assum `typ = r` SUBST_ALL_TAC >>
      rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  Cases_on `string_to_num q = string_to_num id`
  >- (qexists_tac `<|assignable := T; type := tv; value := v'|>` >>
      `r = typ` by metis_tac[] >>
      qpat_x_assum `r = typ` SUBST_ALL_TAC >>
      asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  first_x_assum (qspecl_then [`tenv`, `t`, `m`, `id`, `typ`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id'' typ''. _` (qspecl_then [`id'`, `typ'`] mp_tac) >>
      simp[]) >>
  strip_tac >>
  qexists_tac `entry` >> asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]
QED

Theorem bind_arguments_scope_covers_uint_getter[local]:
  !tenv params vs sc id.
    bind_arguments tenv params vs = SOME sc /\ MEM (id,BaseT (UintT 256)) params /\
    (!id' typ'. MEM (id',typ') params /\ string_to_num id' = string_to_num id ==>
       typ' = BaseT (UintT 256)) ==>
    ?i entry. FLOOKUP sc (string_to_num id) = SOME entry /\
              entry.type = BaseTV (UintT 256) /\ entry.assignable /\
              entry.value = IntV i
Proof
  Induct_on `params` >> simp[Once bind_arguments_def] >>
  Cases >> simp[Once bind_arguments_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  Cases_on `evaluate_type tenv r` >> simp[] >>
  Cases_on `safe_cast x h` >> simp[] >>
  Cases_on `bind_arguments tenv params t` >> simp[] >>
  rpt strip_tac >> gvs[PULL_EXISTS]
  >- (`r = BaseT (UintT 256)` by metis_tac[] >> gvs[evaluate_type_def] >>
      Cases_on `h` >> gvs[vyperValueOperationTheory.safe_cast_def] >>
      qexists_tac `i` >>
      qexists_tac `<|assignable := T; type := BaseTV (UintT 256); value := IntV i|>` >>
      rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  Cases_on `string_to_num q = string_to_num id`
  >- (`r = BaseT (UintT 256)` by metis_tac[] >> gvs[evaluate_type_def] >>
      Cases_on `h` >> gvs[vyperValueOperationTheory.safe_cast_def] >>
      qexists_tac `i` >>
      qexists_tac `<|assignable := T; type := BaseTV (UintT 256); value := IntV i|>` >>
      asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  first_x_assum (qspecl_then [`tenv`, `t`, `x''`, `id`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id'' typ''. _` (qspecl_then [`id'`, `typ'`] mp_tac) >>
      simp[]) >>
  strip_tac >>
  qexists_tac `i` >> qexists_tac `entry` >> asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]
QED
Theorem bind_arguments_scope_covers_generated_uint_ambient:
  !tenv all_args vals scope n.
    bind_arguments tenv all_args vals = SOME scope /\
    MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
    (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
        string_to_num id' = string_to_num id ==> typ' = typ) ==>
    ?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
              entry.type = BaseTV (UintT 256) /\ entry.assignable /\
              entry.value = IntV i
Proof
  rpt strip_tac >>
  irule bind_arguments_scope_covers_uint_getter >>
  qexistsl [`all_args`, `tenv`, `vals`] >>
  simp[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
  simp[]
QED

Theorem bind_arguments_Name_eval_no_type_error[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ string_to_num id' = string_to_num id ==> typ' = typ) /\
  eval_expr cx (Name NoneT id) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params_getter >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, initial_state_def, get_scopes_def,
       lookup_scopes_val_def, bind_def, lift_option_def, lift_option_type_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem bind_arguments_Name_eval_Value[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ string_to_num id' = string_to_num id ==> typ' = typ) /\
  eval_expr cx (Name NoneT id) (initial_state am [scope]) = (INL tvl,st') ==>
  ?v. tvl = Value v
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params_getter >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, initial_state_def, get_scopes_def,
       lookup_scopes_val_def, bind_def, lift_option_def, lift_option_type_def,
       return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem bind_arguments_Name_eval_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] ==>
  ?entry. FLOOKUP scope (string_to_num id) = SOME entry /\
          evaluate_type tenv typ = SOME entry.type /\ entry.assignable /\
          eval_expr cx (Name NoneT id) st = (INL (Value entry.value),st)
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params_getter >> strip_tac >>
  qexists_tac `entry` >>
  gvs[Once evaluate_def, get_scopes_def, lookup_scopes_val_def,
      bind_def, lift_option_def, lift_option_type_def, return_def]
QED

Theorem bind_arguments_generated_Name_eval_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n,typ) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] ==>
  ?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
          evaluate_type tenv typ = SOME entry.type /\ entry.assignable /\
          eval_expr cx (Name NoneT (num_to_dec_string n)) st =
            (INL (Value entry.value),st)
Proof
  rpt strip_tac >>
  irule bind_arguments_Name_eval_post_prefix >>
  simp[] >>
  qexistsl [`args`,`vals`] >> simp[] >>
  metis_tac[]
QED

Theorem evaluate_subscript_hashmap_getter_error_not_TypeError[local]:
  !vt.
    check_value_type tenv vt /\
    evaluate_subscript tenv arr_tv (HashMapRef is_transient slot kt vt) idx = INR err ==>
    !msg. err <> TypeError msg
Proof
  Induct_on `vt` >>
  rw[check_value_type_def, evaluate_subscript_def, AllCaseEqs(), LET_THM] >>
  Cases_on `t` >> gvs[assignable_type_def, well_formed_type_def,
                    evaluate_type_def, AllCaseEqs()]
QED

Theorem evaluate_subscript_getter_error_not_TypeError[local]:
  ((?av i. x = Value (ArrayV av) /\ idx = IntV i) \/
   (?is_transient slot kt vt.
      x = HashMapRef is_transient slot kt vt /\ check_value_type tenv vt) \/
   (?is_transient slot elem_tv bd i.
      x = ArrayRef is_transient slot elem_tv bd /\ idx = IntV i)) /\
  evaluate_subscript tenv arr_tv x idx = INR err ==>
  !msg. err <> TypeError msg
Proof
  rpt strip_tac >> gvs[] >>
  gvs[evaluate_subscript_def, vyperValueOperationTheory.array_index_def, AllCaseEqs(), LET_THM] >>
  TRY (Cases_on `t` >> gvs[check_value_type_def, assignable_type_def,
                          well_formed_type_def, evaluate_type_def, AllCaseEqs()]) >>
  metis_tac[evaluate_subscript_hashmap_getter_error_not_TypeError]
QED

Theorem evaluate_subscript_Value_ArrayV_IntV_error_not_TypeError[local]:
  evaluate_subscript tenv arr_tv (Value (ArrayV av)) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, vyperValueOperationTheory.array_index_def,
     AllCaseEqs(), LET_THM]
QED

Theorem Subscript_NoneTV_HashMapRef_no_TypeError:
  check_value_type (get_tenv cx) vt /\
  (do
     check_array_bounds cx (HashMapRef is_transient base_slot kt vt) kv;
     res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV
              (HashMapRef is_transient base_slot kt vt) kv);
     case res of
     | INL v => return v
     | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
   od) st = (res,st') ==>
  no_type_error_result res
Proof
  rw[check_array_bounds_def, bind_def, ignore_bind_def, return_def,
     raise_def, lift_sum_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `vt` >>
  gvs[evaluate_subscript_def, check_value_type_def,
      assignable_type_def, well_formed_type_def,
      evaluate_type_def, AllCaseEqs(), bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (imp_res_tac assignable_type_well_formed) >>
  TRY (Cases_on `evaluate_type (get_tenv cx) t` >> gvs[well_formed_type_def, bind_def, return_def, raise_def]) >>
  TRY (Cases_on `read_storage_slot cx is_transient
                   (hashmap_slot base_slot (encode_hashmap_key kt kv)) x s''` >>
       gvs[bind_def, return_def, raise_def]) >>
  TRY (Cases_on `q` >> gvs[bind_def, return_def, raise_def]) >>
  TRY (Cases_on `kv` >> gvs[check_array_bounds_def, return_def]) >>
  gvs[check_array_bounds_def, return_def] >>
  TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
       strip_tac >> gvs[])
QED

Theorem materialise_getter_result_no_type_error:
  ((?v. tv = Value v) \/
   (?is_transient base_slot elem_tv bd.
      tv = ArrayRef is_transient base_slot elem_tv bd)) /\
  materialise cx tv st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >> gvs[materialise_def, bind_def, return_def, raise_def,
                       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `read_storage_slot cx is_transient base_slot (ArrayTV elem_tv bd) st` >>
  Cases_on `q` >> gvs[return_def, raise_def] >>
  imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem array_public_getter_tuple_shape:
  is_ArrayT typ /\
  external_getter_tuple src (VariableDecl Public mut id typ init) =
    SOME (gm,gnr,args,dflts,ret,body) ==>
  gm = View /\ gnr = F /\ dflts = [] /\
  ?kt vt exp. build_getter (TopLevelName NoneT (src,id)) kt (Type vt) 0 =
                 (args,ret,exp) /\ body = [Return (SOME exp)]
Proof
  rw[external_getter_tuple_def, getter_def] >>
  Cases_on `build_getter (TopLevelName NoneT (src,id)) (BaseT (UintT 256))
              (Type (ArrayT_type typ)) 0` >>
  Cases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem hashmap_public_getter_tuple_shape:
  external_getter_tuple src (HashMapDecl Public is_transient id kt vt init) =
    SOME (gm,gnr,args,dflts,ret,body) ==>
  gm = View /\ gnr = F /\ dflts = [] /\
  ?exp. build_getter (TopLevelName NoneT (src,id)) kt vt 0 =
          (args,ret,exp) /\ body = [Return (SOME exp)]
Proof
  rw[external_getter_tuple_def, getter_def] >>
  Cases_on `build_getter (TopLevelName NoneT (src,id)) kt vt 0` >>
  Cases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem checked_hashmap_decl_value_type_checked:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts ==>
  check_value_type (type_env_all_modules mods) vt
Proof
  rpt strip_tac >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  gvs[check_toplevel_decl_def]
QED

Theorem checked_public_hashmap_TopLevelName_carrier:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) (initial_state am [scope]) = (INL tvl,st') ==>
  ?slot. tvl = HashMapRef is_transient slot kt vt
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def] >>
  metis_tac[]
QED

Theorem checked_public_hashmap_TopLevelName_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def,
                       vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED


Theorem checked_public_hashmap_TopLevelName_carrier_post_prefix:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) st = (INL tvl,st') ==>
  ?slot. tvl = HashMapRef is_transient slot kt vt
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def] >>
  metis_tac[]
QED

Theorem checked_public_hashmap_TopLevelName_no_type_error_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def,
                       vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED
Theorem build_getter_args_index_ge_aux[local]:
  !e kt vt n args ret exp id typ.
    build_getter e kt vt n = (args,ret,exp) /\ MEM (id,typ) args ==>
    ?m. n <= m /\ id = num_to_dec_string m
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[] >>
  first_x_assum drule >> rw[] >>
  qexists_tac `m` >> simp[]
QED

Theorem string_to_num_eq_imp:
  !s t. string_to_num s = string_to_num t ==> s = t
Proof
  metis_tac[string_to_num_inj]
QED

Theorem build_getter_args_no_current_name:
  !e kt vt n args ret exp typ.
    build_getter e kt vt (SUC n) = (args,ret,exp) /\
    MEM (num_to_dec_string n,typ) args ==> F
Proof
  rpt strip_tac >>
  drule_all build_getter_args_index_ge_aux >>
  strip_tac >>
  gvs[ASCIInumbersTheory.toString_11] >>
  decide_tac
QED

Theorem build_getter_args_no_current_num[local]:
  !e kt vt n args ret exp id typ.
    build_getter e kt vt (SUC n) = (args,ret,exp) /\
    MEM (id,typ) args /\
    string_to_num id = string_to_num (num_to_dec_string n) ==> F
Proof
  rpt strip_tac >>
  drule string_to_num_eq_imp >>
  strip_tac >> gvs[] >>
  metis_tac[build_getter_args_no_current_name]
QED

Theorem build_getter_args_num_unique:
  !e kt vt n args ret exp id typ id' typ'.
    build_getter e kt vt n = (args,ret,exp) /\
    MEM (id,typ) args /\ MEM (id',typ') args /\
    string_to_num id' = string_to_num id ==> typ' = typ
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[] >>
  imp_res_tac string_to_num_eq_imp >>
  gvs[ASCIInumbersTheory.toString_11] >>
  TRY (imp_res_tac build_getter_args_no_current_name) >>
  TRY (imp_res_tac build_getter_args_no_current_num) >>
  metis_tac[]
QED

Theorem build_getter_bound_Name_eval_no_type_error[local]:
  build_getter e kt vt n = (args,ret,exp) /\
  MEM (id,typ) args /\
  bind_arguments tenv args vals = SOME scope /\
  eval_expr cx (Name NoneT id) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule bind_arguments_Name_eval_no_type_error >>
  simp[] >>
  metis_tac[build_getter_args_num_unique]
QED

Theorem build_getter_exp_pure[local]:
  !e kt vt n args ret exp.
    pure_expr e /\ build_getter e kt vt n = (args,ret,exp) ==> pure_expr exp
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def, pure_expr_def] >>
  Cases_on `is_ArrayT vt` >> simp[pure_expr_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[pure_expr_def] >>
  first_x_assum irule >> simp[pure_expr_def]
QED

Theorem build_getter_exp_type_NoneTV[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) /\ evaluate_type tenv (expr_type e) = SOME NoneTV ==>
    evaluate_type tenv (expr_type exp) = SOME NoneTV
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def, expr_type_def, evaluate_type_def] >>
  Cases_on `is_ArrayT vt` >> simp[expr_type_def, evaluate_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[expr_type_def, evaluate_type_def] >>
  first_x_assum irule >> simp[expr_type_def, evaluate_type_def]
QED

Theorem generated_hashmap_subscript_step_no_type_error:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  irule Subscript_NoneTV_HashMapRef_no_TypeError >>
  qexistsl [`slot`, `cx`, `is_transient`, `kt`, `entry.value`,
            `<|immutables := am.immutables; logs := []; scopes := [scope];
               accounts := am.accounts; tStorage := am.tStorage|>`, `st2`, `vt`] >>
  simp[]
QED

Theorem generated_hashmap_subscript_step_no_type_error_params:
  !tenv params vals scope n kt vt cx e am is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  metis_tac[generated_hashmap_subscript_step_no_type_error]
QED


Theorem generated_hashmap_subscript_step_error_no_type_error_params:
  !tenv params vals scope n kt vt cx e am is_transient slot st1 err st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INR err,st2) ==>
  no_type_error_result (INR err)
Proof
  rpt strip_tac >> drule_all generated_hashmap_subscript_step_no_type_error_params >>
  asm_rewrite_tac[] >> strip_tac >>
  fs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED
Theorem generated_hashmap_array_subscript_step_no_type_error_params[local]:
  !tenv params vals scope n kt t b cx e am is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  assignable_type (get_tenv cx) (ArrayT t b) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type (ArrayT t b))),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >> irule generated_hashmap_subscript_step_no_type_error_params >>
  qexistsl [`am`, `cx`, `e`, `is_transient`, `kt`, `n`, `params`, `scope`,
            `slot`, `st1`, `st2`, `tenv`, `vals`, `Type (ArrayT t b)`] >>
  simp[check_value_type_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem generated_hashmap_subscript_step_success_carrier:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (HashMapT kt' vt')),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INL tvl,st2) ==>
  ?slot'. tvl = HashMapRef is_transient slot' kt' vt'
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_array_tail_subscript_success_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) (Type vt) /\ is_ArrayT vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type vt)),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INL tvl,st2) ==>
  (?av. tvl = Value (ArrayV av)) \/
  (?is_transient' slot' elem_tv bd. tvl = ArrayRef is_transient' slot' elem_tv bd)
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  Cases_on `vt` >> gvs[is_ArrayT_def, check_value_type_def,
                        assignable_type_def, well_formed_type_def,
                        evaluate_type_def, AllCaseEqs(), bind_def,
                        return_def, raise_def, IS_SOME_EXISTS] >>
  rename [`evaluate_type (get_tenv cx) t = SOME elem_tv`,
          `type_slot_size (ArrayTV elem_tv bd)`] >>
  gvs[check_array_bounds_def, ignore_bind_def, lift_sum_def,
      evaluate_subscript_def, evaluate_type_def, LET_THM,
      bind_def, return_def, raise_def] >>
  Cases_on `entry.value` >> gvs[check_array_bounds_def, return_def] >>
  Cases_on `read_storage_slot cx is_transient
             (hashmap_slot slot (encode_hashmap_key kt entry.value))
             (ArrayTV elem_tv bd) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[initial_state_def, bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  (`well_formed_type_value (ArrayTV elem_tv bd)` by
    (`evaluate_type (get_tenv cx) (ArrayT t bd) = SOME (ArrayTV elem_tv bd)` by
       simp[evaluate_type_def] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value])) >>
  drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
  strip_tac >>
  Cases_on `x` >> gvs[vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_array_tail_subscript_typed_package:
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  assignable_type (get_tenv cx) elem_ast /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) elem_ast = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type (ArrayT elem_ast bd_ast))),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INL tvl,step_st) ==>
  ((?av bd. tvl = Value (ArrayV av) /\
            value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient' slot' bd. tvl = ArrayRef is_transient' slot' elem_tv bd))
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  gvs[check_array_bounds_def, ignore_bind_def, lift_sum_def,
      evaluate_subscript_def, evaluate_type_def, LET_THM,
      bind_def, return_def, raise_def] >>
  Cases_on `entry.value` >> gvs[check_array_bounds_def, return_def] >>
  Cases_on `0 < type_slot_size elem_tv /\
            type_slot_size (ArrayTV elem_tv bd_ast) < dimword (:256)` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `read_storage_slot cx is_transient
             (hashmap_slot slot (encode_hashmap_key kt entry.value))
             (ArrayTV elem_tv bd_ast) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[initial_state_def, bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  (`well_formed_type_value (ArrayTV elem_tv bd_ast)` by
    (`evaluate_type (get_tenv cx) (ArrayT elem_ast bd_ast) = SOME (ArrayTV elem_tv bd_ast)` by
       simp[evaluate_type_def] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value])) >>
  drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
  strip_tac >>
  Cases_on `x` >> gvs[vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED

Theorem build_getter_args_current[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) ==>
    MEM (num_to_dec_string n,kt) args
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem machine_well_typed_get_source_immutables_value_has_type[local]:
  machine_well_typed am /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  value_has_type tv v /\ well_formed_type_value tv
Proof
  rw[machine_well_typed_def] >>
  Cases_on `ALOOKUP am.immutables tx.target` >> gvs[get_source_immutables_def] >>
  `MEM (tx.target,x) am.immutables` by metis_tac[ALOOKUP_MEM] >>
  `imms_well_typed x` by
    (gvs[EVERY_MEM] >>
     qpat_x_assum `!x. MEM x am.immutables ==> _` (qspec_then `(tx.target,x)` mp_tac) >>
     simp[]) >>
  gvs[imms_well_typed_def, get_source_immutables_def] >>
  Cases_on `ALOOKUP x src` >> gvs[] >>
  metis_tac[]
QED

Theorem checked_public_array_TopLevelName_indexable_carrier[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (INL tvl,st') ==>
  (?av. tvl = Value (ArrayV av)) \/
  (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `typ` >> gvs[is_ArrayT_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `value_has_type x'0 x'1` by
        (gvs[machine_well_typed_def] >>
         `MEM (tx.target,x'') am.immutables` by metis_tac[ALOOKUP_MEM] >>
         `imms_well_typed x''` by
           (gvs[EVERY_MEM] >>
            qpat_x_assum `!x. MEM x am.immutables ==> _` (qspec_then `(tx.target,x'')` mp_tac) >>
            simp[]) >>
         Cases_on `ALOOKUP x'' src` >> gvs[imms_well_typed_def] >>
         metis_tac[]) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `value_has_type x'0 x'1` by
        (gvs[machine_well_typed_def] >>
         `MEM (tx.target,x'') am.immutables` by metis_tac[ALOOKUP_MEM] >>
         `imms_well_typed x''` by
           (gvs[EVERY_MEM] >>
            qpat_x_assum `!x. MEM x am.immutables ==> _` (qspec_then `(tx.target,x'')` mp_tac) >>
            simp[]) >>
         Cases_on `ALOOKUP x'' src` >> gvs[imms_well_typed_def] >>
         metis_tac[]) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T (ArrayT t b),fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
      metis_tac[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F (ArrayT t b),fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
  metis_tac[]
QED


Theorem checked_public_array_TopLevelName_typed_indexable_carrier:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) typ =
    SOME (ArrayTV elem_tv bd) /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv bd))
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `typ` >> gvs[is_ArrayT_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T (ArrayT t b),fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
      metis_tac[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F (ArrayT t b),fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
  metis_tac[]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv b) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv b))
Proof
  rpt strip_tac >>
  irule (Q.INST [`typ` |-> `ArrayT t b`, `bd` |-> `b`]
           checked_public_array_TopLevelName_typed_indexable_carrier) >>
  qexistsl [`am`, `art`, `fn`, `init`, `mods`, `mut`, `scope`, `src`,
            `st'`, `t`, `ts`, `tx`] >>
  simp[is_ArrayT_def, evaluate_type_def, get_tenv_def,
       initial_evaluation_context_def]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) typ =
    SOME (ArrayTV elem_tv bd) /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv bd))
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_evaluation_context_def] >>
  Cases_on `typ` >> gvs[is_ArrayT_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T (ArrayT t b),fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
      metis_tac[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F (ArrayT t b),fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
  metis_tac[]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv b) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv b))
Proof
  rpt strip_tac >>
  irule (Q.INST [`typ` |-> `ArrayT t b`, `bd` |-> `b`]
           checked_public_array_TopLevelName_typed_indexable_carrier_post_prefix) >>
  qexistsl [`am`, `art`, `fn`, `init`, `mods`, `mut`, `src`,
            `st`, `st'`, `t`, `ts`, `tx`] >>
  simp[is_ArrayT_def, evaluate_type_def, get_tenv_def,
       initial_evaluation_context_def]
QED

Theorem checked_public_array_TopLevelName_materialisable_carrier_ArrayT_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  (?v. tvl = Value v) \/
  (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
Proof
  rpt strip_tac >>
  drule_all checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix_any_bd:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
Proof
  rpt strip_tac >>
  drule_all checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix >>
  simp[] >> strip_tac >> gvs[]
  >- (qexists `b` >> simp[]) >>
  metis_tac[]
QED


Theorem all_have_type_oEL_nested_array[local]:
  all_have_type tv vs /\ oEL j vs = SOME v ==> value_has_type tv v
Proof
  rw[vyperTypingTheory.all_have_type_EVERY, oEL_THM, EVERY_EL] >>
  first_x_assum irule >> simp[]
QED

Theorem sparse_has_type_ALOOKUP_nested_array[local]:
  sparse_has_type tv n sparse /\ ALOOKUP sparse k = SOME v ==>
  value_has_type tv v
Proof
  Induct_on `sparse` >> simp[vyperTypingTheory.value_has_type_def] >>
  Cases >> rw[vyperTypingTheory.value_has_type_def] >>
  Cases_on `q = k` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem typed_ArrayV_array_index_nested_carrier[local]:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  array_index (ArrayTV (ArrayTV inner_tv inner_bd) bd) av i = SOME v ==>
  ?av'. v = ArrayV av' /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rpt strip_tac >>
  `value_has_type (ArrayTV inner_tv inner_bd) v` by
    (qspecl_then [`ArrayTV (ArrayTV inner_tv inner_bd) bd`,
                  `ArrayTV inner_tv inner_bd`,`bd`,`av`,`i`,`v`]
       mp_tac vyperAssignPreservesTypeTheory.array_index_has_type >>
     simp[]) >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem typed_ArrayV_array_index_NoneTV_nested_carrier[local]:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  array_index NoneTV av i = SOME v ==>
  ?av'. v = ArrayV av' /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rpt strip_tac >>
  Cases_on `av` >> gvs[vyperValueOperationTheory.array_index_def,
                        vyperTypingTheory.value_has_type_def] >>
  Cases_on `0 <= i` >> gvs[]
  >- (Cases_on `bd` >> gvs[vyperTypingTheory.value_has_type_def] >>
      drule_all all_have_type_oEL_nested_array >> strip_tac >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def])
  >- (Cases_on `bd` >> gvs[AllCaseEqs(), vyperTypingTheory.value_has_type_def] >>
      drule_all sparse_has_type_ALOOKUP_nested_array >> strip_tac >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  drule_all all_have_type_oEL_nested_array >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem evaluate_subscript_typed_Value_ArrayV_nested_carrier[local]:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  evaluate_subscript tenv (ArrayTV (ArrayTV inner_tv inner_bd) bd)
    (Value (ArrayV av)) (IntV i) = INL (INL tvl) ==>
  ?av'. tvl = Value (ArrayV av') /\
        value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rw[evaluate_subscript_def, AllCaseEqs()] >>
  drule_all typed_ArrayV_array_index_nested_carrier >>
  strip_tac >> gvs[]
QED

Theorem evaluate_subscript_NoneTV_Value_ArrayV_nested_carrier:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  evaluate_subscript tenv NoneTV (Value (ArrayV av)) (IntV i) = INL (INL tvl) ==>
  ?av'. tvl = Value (ArrayV av') /\
        value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rw[evaluate_subscript_def, AllCaseEqs()] >>
  drule_all typed_ArrayV_array_index_NoneTV_nested_carrier >>
  strip_tac >> gvs[]
QED


Theorem check_array_bounds_error_not_TypeError_getter[local]:
  check_array_bounds cx tv v st = (INR err,st') ==> !msg. err <> Error (TypeError msg)
Proof
  rpt strip_tac >> Cases_on `tv` >> Cases_on `v` >>
  TRY (Cases_on `b0`) >>
  gvs[check_array_bounds_def, bind_def, return_def, raise_def,
      get_storage_backend_def, check_def, assert_def, AllCaseEqs()] >>
  metis_tac[vyperTypeExprSoundnessTheory.get_storage_backend_no_error]
QED

Theorem check_array_bounds_ArrayRef_error_not_TypeError_getter:
  check_array_bounds cx (ArrayRef is_transient slot elem_tv bd) (IntV i) st =
    (INR err,st') ==>
  !msg. err <> Error (TypeError msg)
Proof
  rpt strip_tac >> Cases_on `bd` >>
  gvs[check_array_bounds_def, bind_def, return_def, raise_def,
      get_storage_backend_def, check_def, assert_def, AllCaseEqs()] >>
  metis_tac[vyperTypeExprSoundnessTheory.get_storage_backend_no_error]
QED

Theorem evaluate_subscript_ArrayRef_nested_carrier[local]:
  evaluate_subscript tenv (ArrayTV (ArrayTV inner_tv inner_bd) bd)
    (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) = INL (INL tvl) ==>
  ?slot'. tvl = ArrayRef is_transient slot' inner_tv inner_bd
Proof
  rw[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM]
QED

Theorem evaluate_subscript_NoneTV_ArrayRef_nested_carrier:
  evaluate_subscript tenv NoneTV
    (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) = INL (INL tvl) ==>
  ?slot'. tvl = ArrayRef is_transient slot' inner_tv inner_bd
Proof
  rw[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM]
QED
Theorem evaluate_subscript_ArrayRef_nested_error_not_TypeError[local]:
  evaluate_subscript tenv (ArrayTV (ArrayTV inner_tv inner_bd) bd)
    (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM]
QED

Theorem generated_array_subscript_step_Value_typed_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV (ArrayTV inner_tv inner_bd) bd) /\
  eval_expr cx e (initial_state am [scope]) = (INL (Value (ArrayV av)),st1) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
   | INR _ => T)
Proof
  rpt strip_tac >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i)
              <|immutables := am.immutables; logs := []; scopes := [scope];
                accounts := am.accounts; tStorage := am.tStorage|>` >>
  rename1 `check_array_bounds _ _ _ _ = (bounds_res,bounds_st)` >>
  Cases_on `bounds_res` >> simp[bind_def, return_def, raise_def]
  >- (Cases_on `evaluate_subscript (get_tenv cx) (ArrayTV (ArrayTV inner_tv inner_bd) bd)
          (Value (ArrayV av)) (IntV i)` >> simp[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >> simp[bind_def, return_def, raise_def] >>
          rpt strip_tac >>
          qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
          qpat_x_assum `check_array_bounds _ _ _ _ = (INL _,bounds_st)` (fn th => simp[th, bind_def, ignore_bind_def, return_def, raise_def]) >>
          rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
          gvs[evaluate_subscript_def, AllCaseEqs()] >>
          drule_all evaluate_subscript_typed_Value_ArrayV_nested_carrier >> simp[]) >>
      strip_tac >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      drule_all evaluate_subscript_Value_ArrayV_IntV_error_not_TypeError >> simp[]) >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[check_array_bounds_def, return_def, raise_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) (ArrayTV (ArrayTV inner_tv inner_bd) bd)
              (Value (ArrayV av)) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x` >> gvs[bind_def, return_def, raise_def] >>
      gvs[evaluate_subscript_def, AllCaseEqs()] >>
      drule_all typed_ArrayV_array_index_nested_carrier >> simp[])
QED

Theorem generated_array_subscript_step_ArrayRef_typed_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV (ArrayTV inner_tv inner_bd) bd) /\
  eval_expr cx e (initial_state am [scope]) = (INL (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd),st1) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' => ?slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd
   | INR _ => T)
Proof
  rpt strip_tac >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)
              <|immutables := am.immutables; logs := []; scopes := [scope];
                accounts := am.accounts; tStorage := am.tStorage|>` >>
  rename1 `check_array_bounds _ _ _ _ = (bounds_res,bounds_st)` >>
  Cases_on `bounds_res`
  >- (Cases_on `evaluate_subscript (get_tenv cx) (ArrayTV (ArrayTV inner_tv inner_bd) bd)
          (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)` >>
      simp[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >> simp[bind_def, return_def, raise_def] >>
          rpt strip_tac >>
          qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
          simp[bind_def, ignore_bind_def, return_def, raise_def] >>
          rpt strip_tac >>
          gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
          gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM] >>
          drule_all evaluate_subscript_ArrayRef_nested_carrier >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
      simp[bind_def, ignore_bind_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      drule_all evaluate_subscript_ArrayRef_nested_error_not_TypeError >> simp[]) >>
  simp[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `bd` >>
  gvs[check_array_bounds_def, bind_def, return_def, raise_def,
      get_storage_backend_def, check_def, assert_def, AllCaseEqs()] >>
  gvs[vyperTypeExprSoundnessTheory.get_storage_backend_no_error] >>
  gvs[evaluate_subscript_def, lift_sum_def, bind_def, ignore_bind_def,
      return_def, raise_def, bound_length_def, AllCaseEqs(), LET_THM] >>
  Cases_on `0 <= i /\ Num i < n'` >>
  gvs[bind_def, return_def, raise_def, AllCaseEqs(), LET_THM]
QED

Theorem generated_array_subscript_step_typed_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV (ArrayTV inner_tv inner_bd) bd) /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd)) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd))
   | INR _ => T)
Proof
  rpt strip_tac >> gvs[]
  >- (drule_all_then assume_tac generated_array_subscript_step_Value_typed_carrier >> gvs[])
  >- (drule_all_then assume_tac generated_array_subscript_step_Value_typed_carrier >> Cases_on `res` >> gvs[])
  >- (drule_all_then assume_tac generated_array_subscript_step_ArrayRef_typed_carrier >> gvs[]) >>
  drule_all_then assume_tac generated_array_subscript_step_ArrayRef_typed_carrier >> Cases_on `res` >> gvs[]
QED
Theorem build_getter_recursive_base_expr_type_NoneTV_probe[local]:
  evaluate_type tenv (expr_type (Subscript NoneT e idx)) = SOME NoneTV
Proof
  simp[expr_type_def, evaluate_type_def]
QED

Theorem generated_outer_subscript_uses_NoneTV_probe[local]:
  eval_expr cx (Subscript NoneT e idx1) st = (INL tvl,st1) /\
  eval_expr cx idx2 st1 = (INL (Value v),st2) ==>
  eval_expr cx (Subscript NoneT (Subscript NoneT e idx1) idx2) st =
    (do
       check_array_bounds cx tvl v;
       res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV tvl v);
       case res of
       | INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od) st2
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def,
       lift_option_type_def, expr_type_def, evaluate_type_def]
QED

Theorem evaluate_subscript_NoneTV_Value_ArrayV_result_probe[local]:
  evaluate_subscript tenv NoneTV (Value (ArrayV av)) (IntV i) =
    (case array_index NoneTV av i of
     | SOME v => INL (INL (Value v))
     | NONE => INR (RuntimeError "subscript array_index"))
Proof
  simp[evaluate_subscript_def]
QED

Theorem evaluate_subscript_NoneTV_Value_ArrayV_error_not_TypeError_probe[local]:
  evaluate_subscript tenv NoneTV (Value (ArrayV av)) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, AllCaseEqs()]
QED

Theorem evaluate_subscript_NoneTV_ArrayRef_result_probe[local]:
  evaluate_subscript tenv NoneTV (ArrayRef is_transient base_slot elem_tv bd) (IntV i) =
    (if 0 <= i /\ Num i < bound_length bd then
       let elem_offset = (case bd of Fixed _ => 0 | Dynamic _ => 1) in
       let slot = base_slot + n2w (elem_offset + Num i * type_slot_size elem_tv) in
       case elem_tv of
       | ArrayTV inner_tv inner_bd => INL (INL (ArrayRef is_transient slot inner_tv inner_bd))
       | _ => INL (INR (is_transient,slot,elem_tv))
     else INR (RuntimeError "subscript array out of bounds"))
Proof
  rw[evaluate_subscript_def]
QED

Theorem evaluate_subscript_NoneTV_ArrayRef_error_not_TypeError_probe[local]:
  evaluate_subscript tenv NoneTV (ArrayRef is_transient base_slot elem_tv bd) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, AllCaseEqs(), LET_THM]
QED

Theorem Subscript_NoneTV_Value_ArrayV_no_TypeError[local]:
  (do
     check_array_bounds cx (Value (ArrayV av)) (IntV i);
     res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV (Value (ArrayV av)) (IntV i));
     case res of
     | INL v => return v
     | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
   od) st = (res,st') ==>
  no_type_error_result res
Proof
  rw[check_array_bounds_def, evaluate_subscript_def, lift_sum_def,
     bind_def, ignore_bind_def, return_def, raise_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def,
     AllCaseEqs()] >>
  Cases_on `array_index NoneTV av i` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem Subscript_NoneTV_ArrayRef_no_TypeError[local]:
  (do
     check_array_bounds cx (ArrayRef is_transient base_slot elem_tv bd) (IntV i);
     res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV (ArrayRef is_transient base_slot elem_tv bd) (IntV i));
     case res of
     | INL v => return v
     | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
   od) st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient base_slot elem_tv bd) (IntV i) st` >>
  rename1 `check_array_bounds _ _ _ _ = (bounds_res,bounds_st)` >>
  Cases_on `bounds_res`
  >- (qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
      simp[evaluate_subscript_def, lift_sum_def, bind_def, ignore_bind_def,
           return_def, raise_def, bound_length_def, AllCaseEqs(), LET_THM] >>
      rpt strip_tac >>
      gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `elem_tv` >>
      Cases_on `0 <= i /\ Num i < bound_length bd` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def,
          AllCaseEqs(), LET_THM] >>
      TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error) >>
      strip_tac >> gvs[]) >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  metis_tac[check_array_bounds_error_not_TypeError_getter]
QED

Theorem generated_array_subscript_step_NoneTV_carrier_no_type_error:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac
  >- (drule Subscript_NoneTV_Value_ArrayV_no_TypeError >>
      simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  drule Subscript_NoneTV_ArrayRef_no_TypeError >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED


Theorem generated_array_subscript_step_NoneTV_materialisable:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' => (?v. tvl' = Value v) \/
                  (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error] >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          lift_sum_def, evaluate_subscript_def, AllCaseEqs()] >>
      Cases_on `array_index NoneTV av i` >>
      gvs[bind_def, return_def, raise_def]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot elem_tv bd) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot elem_tv bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >> gvs[bind_def, return_def, raise_def]
      >- gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
              vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `y` >> gvs[bind_def, return_def, raise_def] >>
      Cases_on `r` >> gvs[bind_def, return_def, raise_def,
                            vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  metis_tac[check_array_bounds_error_not_TypeError_getter]
QED

Theorem generated_array_subscript_step_NoneTV_carrier_no_type_error_post_prefix:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (irule bind_arguments_scope_covers_generated_uint_ambient >>
     qexistsl [`args`,`tenv`,`vals`] >> simp[] >> metis_tac[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac
  >- (drule Subscript_NoneTV_Value_ArrayV_no_TypeError >>
      simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  drule Subscript_NoneTV_ArrayRef_no_TypeError >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem generated_array_subscript_step_NoneTV_materialisable_post_prefix:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' => (?v. tvl' = Value v) \/
                  (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error_post_prefix] >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (irule bind_arguments_scope_covers_generated_uint_ambient >>
     qexistsl [`args`,`tenv`,`vals`] >> simp[] >> metis_tac[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i) st` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          lift_sum_def, evaluate_subscript_def, AllCaseEqs()] >>
      Cases_on `array_index NoneTV av i` >>
      gvs[bind_def, return_def, raise_def]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot elem_tv bd) (IntV i) st` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot elem_tv bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >> gvs[bind_def, return_def, raise_def]
      >- gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
              vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `y` >> gvs[bind_def, return_def, raise_def] >>
      Cases_on `r` >> gvs[bind_def, return_def, raise_def,
                            vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  metis_tac[check_array_bounds_error_not_TypeError_getter]
QED

Theorem generated_array_subscript_step_NoneTV_nested_carrier:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd)) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >-
    (FIRST [irule generated_array_subscript_step_NoneTV_carrier_no_type_error,
            irule (cj 2 generated_array_subscript_step_NoneTV_materialisable)] >>
     gvs[] >> metis_tac[]) >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
      Cases_on `evaluate_subscript (get_tenv cx) NoneTV (Value (ArrayV av)) (IntV i)` >>
      gvs[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >>
          gvs[bind_def, return_def, raise_def,
              vyperTypeExprSoundnessTheory.no_type_error_result_def]
          >- (drule_all evaluate_subscript_NoneTV_Value_ArrayV_nested_carrier >>
              strip_tac >> metis_tac[]) >>
          gvs[evaluate_subscript_def, AllCaseEqs()]) >>
      gvs[evaluate_subscript_def, AllCaseEqs()]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >>
      gvs[bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      TRY (Cases_on `x` >> gvs[bind_def, return_def, raise_def,
                               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `y'` >> gvs[bind_def, return_def, raise_def,
                                 vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `r'` >> gvs[bind_def, return_def, raise_def,
                                vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `read_storage_slot cx q q' r'' r` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `q''` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
           strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
      TRY (drule_all evaluate_subscript_NoneTV_ArrayRef_nested_carrier >>
           strip_tac >> metis_tac[])) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule check_array_bounds_ArrayRef_error_not_TypeError_getter >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
QED

Theorem eval_stmts_single_Return_no_type_error:
  eval_expr cx e st = (expr_res,st1) /\
  no_type_error_result expr_res /\

  (!tv mat_res st2.
     expr_res = INL tv /\ materialise cx tv st1 = (mat_res,st2) ==>
     no_type_error_result mat_res) /\
  eval_stmts cx [Return (SOME e)] st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def, bind_def, ignore_bind_def,
       return_def, raise_def] >>
  Cases_on `expr_res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `materialise cx x st1` >> gvs[return_def, raise_def] >>
  Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >> gvs[]
QED

