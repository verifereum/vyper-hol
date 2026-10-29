(*
 * Public getter soundness helpers for checked contracts.
 *
 * This theory proves external lookup/provenance facts and generated scalar,
 * hashmap, and array public-getter no-TypeError helpers used by the final
 * checked external-call theorem.
 *)

Theory vyperTypeContractGetter
Ancestors
  list rich_list arithmetic finite_map alist option pair
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeInitialState vyperPureExpr vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperScopePreservation vyperStatePreservation
  vyperTypeContractStaticMaps vyperTypeContractContext
Libs
  wordsLib

val _ = Parse.hide "body";

(* ===== Allocated-module facts ===== *)

Theorem allocated_toplevel_vtype_VariableDecl[local]:
  check_contract F (layouts:(address # (storage_layout # storage_layout)) list)
    (addr:address) mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  module_allocated layouts addr src ts /\
  MEM (VariableDecl vis mut id ty init) ts ==>
  FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty)
Proof
  strip_tac >> drule_all module_allocated_VariableDecl_slots >> strip_tac >>
  drule check_contract_toplevel_vtype_VariableDecl >>
  disch_then drule >> disch_then drule >> simp[]
QED

Theorem allocated_toplevel_vtype_HashMapDecl[local]:
  check_contract F (layouts:(address # (storage_layout # storage_layout)) list)
    (addr:address) mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  module_allocated layouts addr src ts /\
  MEM (HashMapDecl vis is_transient id kt vt init) ts ==>
  FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (HashMapT kt vt)
Proof
  strip_tac >> drule_all module_allocated_HashMapDecl_slot >> strip_tac >>
  drule check_contract_toplevel_vtype_HashMapDecl >>
  disch_then drule >> disch_then drule >> simp[]
QED

Definition is_public_getter_decl_def:
  is_public_getter_decl fn (VariableDecl Public mut id typ init) = (id = fn) /\
  is_public_getter_decl fn (HashMapDecl Public is_transient id kt vt init) = (id = fn) /\
  is_public_getter_decl _ _ = F
End

Definition external_getter_tuple_def:
  external_getter_tuple src (VariableDecl Public mut id typ init) =
    (if ~is_ArrayT typ then
       SOME (View,F,[],[],typ,[Return (SOME (TopLevelName typ (src,id)))])
     else
       SOME (getter (TopLevelName typ (src,id)) (BaseT (UintT 256)) (Type (ArrayT_type typ)))) /\
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
  FLOOKUP env.toplevel_vtypes (src,fn) = SOME (Type typ) ==>
  type_stmts env typ [Return (SOME (TopLevelName NoneT (src,fn)))] = NONE
Proof
  rw[type_stmt_def, well_typed_expr_def]
QED

Theorem raw_getter_index_name_annotation_contradiction[local]:
  kt <> NoneT /\
  FLOOKUP env.var_types vn = SOME kt ==>
  ~well_typed_expr env (Name NoneT vn)
Proof
  rw[well_typed_expr_def]
QED

Theorem checked_scalar_public_getter_body_typing_package_contradiction[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  ~is_ArrayT typ ==>
  ~(?env_after.
      type_stmts (artifact_env art mods src) typ
        [Return (SOME (TopLevelName NoneT (src,fn)))] = SOME env_after)
Proof
  rw[] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,fn) = SOME (Type typ)` by
    (drule_all allocated_toplevel_vtype_VariableDecl >> simp[]) >>
  `check_toplevel_decl mods art src
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
(* ===== Scalar public getter helpers ===== *)

Theorem checked_scalar_public_getter_eval_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,fn) = SOME (Type typ)` by
    (drule_all allocated_toplevel_vtype_VariableDecl >> simp[]) >>
  `check_toplevel_decl mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
  drule_all module_allocated_VariableDecl_slots >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_name fn ts = NONE` by
        (irule find_var_decl_by_name_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_name fn ts = NONE` by
        (irule find_var_decl_by_name_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_name fn ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_name_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_namespaces_ok] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
      imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  `find_var_decl_by_name fn ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_name_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_namespaces_ok] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem read_storage_result_safe[local]:
  read_result cx (PlaceR (StoragePlace tr slot tv)) st = (rr,sr) ==>
  sr = st /\ no_type_error_result rr
Proof
  strip_tac >> conj_tac
  >- metis_tac[read_result_state] >>
  Cases_on `rr` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[read_result_def, read_place_def] >>
  drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
  strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem checked_scalar_public_getter_eval_no_type_error_materialisable:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL pv =>
     (!rr sr. read_result (initial_evaluation_context am.sources am.layouts tx src)
                pv st' = (rr,sr) ==> sr = st' /\ no_type_error_result rr)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule checked_scalar_public_getter_eval_no_type_error >> metis_tac[]) >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,fn) = SOME (Type typ)` by
    (drule_all allocated_toplevel_vtype_VariableDecl >> simp[]) >>
  `check_toplevel_decl mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
  drule_all module_allocated_VariableDecl_slots >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_name fn ts = NONE` by
        (irule find_var_decl_by_name_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[read_result_def, read_place_def, get_immutables_def,
          get_address_immutables_def, get_source_immutables_def,
          lift_option_def, lift_option_type_def, lift_sum_def,
          bind_def, return_def, raise_def, evaluate_subscripts_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_name fn ts = NONE` by
        (irule find_var_decl_by_name_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[read_result_def, read_place_def, get_immutables_def,
          get_address_immutables_def, get_source_immutables_def,
          lift_option_def, lift_option_type_def, lift_sum_def,
          bind_def, return_def, raise_def, evaluate_subscripts_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_name fn ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_name_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_namespaces_ok] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[read_storage_result_safe]) >>
  `find_var_decl_by_name fn ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_name_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_namespaces_ok] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[read_storage_result_safe]
QED

Theorem checked_scalar_public_getter_eval_no_type_error_materialisable_post_prefix:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL pv =>
     (!rr sr. read_result (initial_evaluation_context am.sources am.layouts tx src)
                pv st' = (rr,sr) ==> sr = st' /\ no_type_error_result rr)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
      simp[get_module_code_def, initial_evaluation_context_def] >>
    `FLOOKUP art.cta_toplevel_vtypes (src,fn) = SOME (Type typ)` by
      (drule_all allocated_toplevel_vtype_VariableDecl >> simp[]) >>
    `check_toplevel_decl mods art src
       (VariableDecl Public mut fn typ init)` by
      metis_tac[check_contract_toplevel_decl_MEM] >>
    `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
      (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
       metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
    drule_all module_allocated_VariableDecl_slots >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
         return_def, raise_def, initial_evaluation_context_def] >>
    Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                          well_formed_type_def]
    >- (`find_var_decl_by_name fn ts = NONE` by
          (irule find_var_decl_by_name_NONE_Constant >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,fn) = SOME (expr_type e)` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`fn`,`expr_type e`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_name fn ts = NONE` by
          (irule find_var_decl_by_name_NONE_Immutable >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,fn) = SOME typ` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`fn`,`typ`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_name fn ts =
           SOME (StorageVarDecl T typ,fn)` by
          metis_tac[find_var_decl_by_name_SOME_storage_var_Transient,
                    contract_namespaces_ok_module_toplevel_vtype_keys,
                    ALOOKUP_MEM, check_contract_namespaces_ok] >>
        gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
            get_tenv_def, initial_evaluation_context_def] >>
        drule assignable_type_well_formed >> simp[well_formed_type_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
        gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
        imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
        gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
    `find_var_decl_by_name fn ts =
       SOME (StorageVarDecl F typ,fn)` by
      metis_tac[find_var_decl_by_name_SOME_storage_var_Storage,
                contract_namespaces_ok_module_toplevel_vtype_keys,
                ALOOKUP_MEM, check_contract_namespaces_ok] >>
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
  `FLOOKUP art.cta_toplevel_vtypes (src,fn) = SOME (Type typ)` by
    (drule_all allocated_toplevel_vtype_VariableDecl >> simp[]) >>
  `check_toplevel_decl mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
  drule_all module_allocated_VariableDecl_slots >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_name fn ts = NONE` by
        (irule find_var_decl_by_name_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[read_result_def, read_place_def, get_immutables_def,
          get_address_immutables_def, get_source_immutables_def,
          lift_option_def, lift_option_type_def, lift_sum_def,
          bind_def, return_def, raise_def, evaluate_subscripts_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_name fn ts = NONE` by
        (irule find_var_decl_by_name_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[read_result_def, read_place_def, get_immutables_def,
          get_address_immutables_def, get_source_immutables_def,
          lift_option_def, lift_option_type_def, lift_sum_def,
          bind_def, return_def, raise_def, evaluate_subscripts_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_name fn ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_name_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_namespaces_ok] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[read_storage_result_safe]) >>
  `find_var_decl_by_name fn ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_name_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_namespaces_ok] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[read_storage_result_safe]
QED


Theorem bind_arguments_scope_covers_uint_getter[local]:
  !tenv params vs sc id.
    bind_arguments tenv params vs = SOME sc /\ MEM (id,BaseT (UintT 256)) params /\
    (!id' typ'. MEM (id',typ') params /\ id' = id ==>
       typ' = BaseT (UintT 256)) ==>
    ?i entry. FLOOKUP sc id = SOME entry /\
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
      qexists_tac `<|assignable := T; type := BaseTV (UintT 256); value := IntV i; popped := []|>` >>
      rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  Cases_on `q = id`
  >- (`r = BaseT (UintT 256)` by metis_tac[] >> gvs[evaluate_type_def] >>
      Cases_on `h` >> gvs[vyperValueOperationTheory.safe_cast_def] >>
      qexists_tac `i` >>
      qexists_tac `<|assignable := T; type := BaseTV (UintT 256); value := IntV i; popped := []|>` >>
      asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  first_x_assum (qspecl_then [`tenv`, `t`, `x''`, `id`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >> simp[] >> metis_tac[]) >>
  strip_tac >>
  qexists_tac `i` >> qexists_tac `entry` >> asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]
QED
Theorem bind_arguments_scope_covers_generated_uint_ambient:
  !tenv all_args vals scope n.
    bind_arguments tenv all_args vals = SOME scope /\
    MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
    (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
        id' = id ==> typ' = typ) ==>
    ?i entry. FLOOKUP scope (num_to_dec_string n) = SOME entry /\
              entry.type = BaseTV (UintT 256) /\ entry.assignable /\
              entry.value = IntV i
Proof
  rpt strip_tac >>
  irule bind_arguments_scope_covers_uint_getter >>
  qexistsl [`all_args`, `tenv`, `vals`] >>
  simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!id typ id' typ'. _`
    (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`,
                  `num_to_dec_string n`, `typ'`] mp_tac) >>
  simp[]
QED

Theorem bind_arguments_Name_eval_no_type_error[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ id' = id ==> typ' = typ) /\
  eval_expr cx (Name NoneT id) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, initial_state_def, get_scopes_def,
       lookup_scopes_def, ignore_bind_def, type_check_def, assert_def,
       lookup_scopes_val_def, bind_def, lift_option_def, lift_option_type_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem bind_arguments_Name_eval_place[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ id' = id ==> typ' = typ) /\
  eval_expr cx (Name NoneT id) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (INL tvl,st') ==>
  tvl = PlaceR (MemoryPlace id []) /\
  st' = (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) /\
  ?entry. FLOOKUP scope id = SOME entry /\
    evaluate_type tenv typ = SOME entry.type /\ entry.assignable /\
    read_result cx tvl st' = (INL entry.value,st')
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, initial_state_def, get_scopes_def,
       lookup_scopes_def, ignore_bind_def, type_check_def, assert_def,
       lookup_scopes_val_def, bind_def, lift_option_def, lift_option_type_def,
       return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  simp[read_result_def, read_place_def, get_scopes_def, lookup_scopes_def,
       read_memory_path_def, evaluate_subscripts_def, lift_option_type_def,
       lift_sum_def, bind_def, return_def]
QED

Theorem bind_arguments_Name_eval_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ id' = id ==> typ' = typ) /\
  st.scopes = [scope] ==>
  ?entry. FLOOKUP scope id = SOME entry /\
          evaluate_type tenv typ = SOME entry.type /\ entry.assignable /\
          eval_expr cx (Name NoneT id) st = (INL (PlaceR (MemoryPlace id [])),st) /\
          read_result cx (PlaceR (MemoryPlace id [])) st = (INL entry.value,st)
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params >> strip_tac >>
  qexists_tac `entry` >>
  gvs[Once evaluate_def, get_scopes_def, lookup_scopes_def,
      ignore_bind_def, type_check_def, assert_def, read_result_def, read_place_def,
      read_memory_path_def, evaluate_subscripts_def, lift_sum_def,
      bind_def, lift_option_def, lift_option_type_def, return_def]
QED

Theorem bind_arguments_generated_Name_eval_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n,typ) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      id' = id ==> typ' = typ) /\
  st.scopes = [scope] ==>
  ?entry. FLOOKUP scope (num_to_dec_string n) = SOME entry /\
          evaluate_type tenv typ = SOME entry.type /\ entry.assignable /\
          eval_expr cx (Name NoneT (num_to_dec_string n)) st =
            (INL (PlaceR (MemoryPlace (num_to_dec_string n) [])),st) /\
          read_result cx (PlaceR (MemoryPlace (num_to_dec_string n) [])) st =
            (INL entry.value,st)
Proof
  rpt strip_tac >>
  irule bind_arguments_Name_eval_post_prefix >>
  simp[] >>
  qexistsl [`args`,`vals`] >> simp[] >>
  metis_tac[]
QED

(* ===== HashMap public getter helpers ===== *)


Theorem array_public_getter_tuple_shape:
  is_ArrayT typ /\
  external_getter_tuple src (VariableDecl Public mut id typ init) =
    SOME (gm,gnr,args,dflts,ret,body) ==>
  gm = View /\ gnr = F /\ dflts = [] /\
  ?kt vt exp. build_getter (TopLevelName typ (src,id)) kt (Type vt) 0 =
                 (args,ret,exp) /\ body = [Return (SOME exp)]
Proof
  rw[external_getter_tuple_def, getter_def] >>
  Cases_on `build_getter (TopLevelName typ (src,id)) (BaseT (UintT 256))
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
  `check_toplevel_decl mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  gvs[check_toplevel_decl_def]
QED

Theorem checked_public_hashmap_TopLevelName_carrier:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (INL tvl,st') ==>
  ?slot. tvl = HashMapRef is_transient slot kt vt
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
  `find_var_decl_by_name id ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_name_SOME_hashmap] >>
  `check_toplevel_decl mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  drule_all module_allocated_HashMapDecl_slot >> strip_tac >>
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
  module_allocated am.layouts tx.target src ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
  `find_var_decl_by_name id ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_name_SOME_hashmap] >>
  `check_toplevel_decl mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  drule_all module_allocated_HashMapDecl_slot >> strip_tac >>
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
  module_allocated am.layouts tx.target src ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) st = (INL tvl,st') ==>
  ?slot. tvl = HashMapRef is_transient slot kt vt
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
  `find_var_decl_by_name id ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_name_SOME_hashmap] >>
  `check_toplevel_decl mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  drule_all module_allocated_HashMapDecl_slot >> strip_tac >>
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
  module_allocated am.layouts tx.target src ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     metis_tac[check_contract_namespaces_ok, ALOOKUP_MEM]) >>
  `find_var_decl_by_name id ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_name_SOME_hashmap] >>
  `check_toplevel_decl mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  drule_all module_allocated_HashMapDecl_slot >> strip_tac >>
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


Theorem build_getter_args_name_unique:
  !e kt vt n args ret exp id typ id' typ'.
    build_getter e kt vt n = (args,ret,exp) /\
    MEM (id,typ) args /\ MEM (id',typ') args /\
    id' = id ==> typ' = typ
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[] >>
  gvs[ASCIInumbersTheory.toString_11] >>
  TRY (imp_res_tac build_getter_args_no_current_name) >>
  metis_tac[]
QED

Theorem build_getter_bound_Name_eval_no_type_error[local]:
  build_getter e kt vt n = (args,ret,exp) /\
  MEM (id,typ) args /\
  bind_arguments tenv args vals = SOME scope /\
  eval_expr cx (Name NoneT id) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule bind_arguments_Name_eval_no_type_error >>
  simp[] >>
  metis_tac[build_getter_args_name_unique]
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

Theorem build_getter_exp_type[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) ==> expr_type exp = ret
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def, expr_type_def] >>
  Cases_on `is_ArrayT vt` >> simp[expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[expr_type_def] >>
  first_x_assum irule >> simp[expr_type_def]
QED

Theorem getter_vtype_annotation_ok[local]:
  !vt. vtype_annotation_ok vt (getter_vtype_annotation vt)
Proof
  Cases_on `vt` >> simp[getter_vtype_annotation_def, vtype_annotation_ok_def]
QED

Theorem check_value_type_subscript[local]:
  !tenv vt kt child.
    check_value_type tenv vt /\
    subscript_vtype vt kt = SOME child ==>
    check_value_type tenv child
Proof
  Cases_on `vt`
  >- (Cases_on `t` >>
      simp[subscript_vtype_def, check_value_type_def,
           Once assignable_type_def]) >>
  simp[subscript_vtype_def, check_value_type_def]
QED

Theorem generated_subscript_type_place[local]:
  type_place_expr env e = SOME container_vt /\
  subscript_vtype container_vt kt = SOME vt /\
  FLOOKUP env.var_types id = SOME kt ==>
  type_place_expr env
    (Subscript (getter_vtype_annotation vt) e (Name kt id)) = SOME vt
Proof
  simp[well_typed_expr_def, expr_type_def, getter_vtype_annotation_ok]
QED

Theorem generated_subscript_well_typed_Type[local]:
  type_place_expr env e = SOME container_vt /\
  subscript_vtype container_vt kt = SOME (Type ty) /\
  check_value_type env.type_defs (Type ty) /\
  FLOOKUP env.var_types id = SOME kt ==>
  well_typed_expr env (Subscript ty e (Name kt id)) /\
  type_place_expr env (Subscript ty e (Name kt id)) = SOME (Type ty)
Proof
  rpt strip_tac >>
  `well_formed_type env.type_defs ty` by
    (qpat_x_assum `check_value_type _ (Type _)` mp_tac >>
     simp[check_value_type_def] >>
     metis_tac[assignable_type_well_formed]) >>
  simp[well_typed_expr_def, expr_type_def, vtype_annotation_ok_def]
QED


Theorem generated_array_getter_transition[local]:
  !env e container_vt kt vt id.
    is_ArrayT vt /\
    type_place_expr env e = SOME container_vt /\
    subscript_vtype container_vt kt = SOME (Type vt) /\
    check_value_type env.type_defs (Type vt) /\
    FLOOKUP env.var_types id = SOME kt ==>
    type_place_expr env (Subscript vt e (Name kt id)) = SOME (Type vt) /\
    subscript_vtype (Type vt) (BaseT (UintT 256)) =
      SOME (Type (ArrayT_type vt)) /\
    check_value_type env.type_defs (Type (ArrayT_type vt))
Proof
  rpt strip_tac >>
  `type_place_expr env
     (Subscript (getter_vtype_annotation (Type vt)) e (Name kt id)) =
     SOME (Type vt)` by
    (irule generated_subscript_type_place >> simp[]) >>
  gvs[getter_vtype_annotation_def] >>
  `subscript_vtype (Type vt) (BaseT (UintT 256)) =
     SOME (Type (ArrayT_type vt))` by
    (Cases_on `vt` >>
     gvs[is_ArrayT_def, ArrayT_type_def, subscript_vtype_def]) >>
  `check_value_type env.type_defs (Type (ArrayT_type vt))` by
    metis_tac[check_value_type_subscript] >>
  simp[]
QED

Theorem generated_hashmap_getter_transition[local]:
  !env e container_vt kt typ vtyp id.
    type_place_expr env e = SOME container_vt /\
    subscript_vtype container_vt kt = SOME (HashMapT typ vtyp) /\
    check_value_type env.type_defs (HashMapT typ vtyp) /\
    FLOOKUP env.var_types id = SOME kt ==>
    type_place_expr env
      (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
         (Name kt id)) = SOME (HashMapT typ vtyp) /\
    subscript_vtype (HashMapT typ vtyp) typ = SOME vtyp /\
    check_value_type env.type_defs vtyp
Proof
  rpt strip_tac >>
  `type_place_expr env
     (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
        (Name kt id)) = SOME (HashMapT typ vtyp)` by
    (irule generated_subscript_type_place >> simp[]) >>
  `hashmap_key_type typ /\ check_value_type env.type_defs vtyp` by
    (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
     simp[check_value_type_def]) >>
  simp[subscript_vtype_def]
QED

Theorem build_getter_result_exists[local]:
  !e kt vt n. ?args ret exp. build_getter e kt vt n = (args,ret,exp)
Proof
  rpt gen_tac >>
  Cases_on `build_getter e kt vt n` >>
  Cases_on `r` >> simp[]
QED

Theorem build_getter_input_ind[local]:
  !P.
    (!e kt vt n.
       (!vn. vn = num_to_dec_string n /\ is_ArrayT vt ==>
         P (Subscript vt e (Name kt vn))
           (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n)) ==>
       P e kt (Type vt) n) /\
    (!e kt typ vtyp n.
       (!vn. vn = num_to_dec_string n ==>
         P (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
              (Name kt vn)) typ vtyp (SUC n)) ==>
       P e kt (HashMapT typ vtyp) n) ==>
    !e kt vt n. P e kt vt n
Proof
  gen_tac >> strip_tac >>
  recInduct build_getter_ind >>
  metis_tac[build_getter_result_exists]
QED


Theorem build_getter_well_typed_Type_array_case[local]:
  !e kt vt n.
    is_ArrayT vt /\
    (!args ret exp env container_vt.
       build_getter
         (Subscript vt e (Name kt (num_to_dec_string n)))
         (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n) =
         (args,ret,exp) /\
       type_place_expr env
         (Subscript vt e (Name kt (num_to_dec_string n))) =
         SOME container_vt /\
       subscript_vtype container_vt (BaseT (UintT 256)) =
         SOME (Type (ArrayT_type vt)) /\
       check_value_type env.type_defs (Type (ArrayT_type vt)) /\
       (!id ty. MEM (id,ty) args ==>
          FLOOKUP env.var_types id = SOME ty) ==>
       well_typed_expr env exp /\ expr_type exp = ret /\
       type_place_expr env exp = SOME (Type ret)) ==>
    !args ret exp env container_vt.
      build_getter e kt (Type vt) n = (args,ret,exp) /\
      type_place_expr env e = SOME container_vt /\
      subscript_vtype container_vt kt = SOME (Type vt) /\
      check_value_type env.type_defs (Type vt) /\
      (!id ty. MEM (id,ty) args ==>
         FLOOKUP env.var_types id = SOME ty) ==>
      well_typed_expr env exp /\ expr_type exp = ret /\
      type_place_expr env exp = SOME (Type ret)
Proof
  rpt strip_tac >>
  qpat_x_assum `build_getter e kt (Type vt) n = _` mp_tac >>
  simp[Once build_getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  `FLOOKUP env.var_types (num_to_dec_string n) = SOME kt` by
    (qpat_assum `!id ty. (_ \/ MEM (id,ty) args') ==> _`
       (qspecl_then [`num_to_dec_string n`,`kt`] mp_tac) >>
     simp[]) >>
  `!id ty. MEM (id,ty) args' ==>
     FLOOKUP env.var_types id = SOME ty` by
    (rpt strip_tac >>
     qpat_assum `!id ty. (_ \/ MEM (id,ty) args') ==> _`
       (qspecl_then [`id`,`ty`] mp_tac) >>
     simp[]) >>
  `type_place_expr env (Subscript vt e (Name kt (num_to_dec_string n))) =
       SOME (Type vt) /\
   subscript_vtype (Type vt) (BaseT (UintT 256)) =
       SOME (Type (ArrayT_type vt)) /\
   check_value_type env.type_defs (Type (ArrayT_type vt))` by
    (irule generated_array_getter_transition >> simp[]) >>
  qpat_assum `!env' container_vt'. _ ==> _`
    (qspecl_then [`env`,`Type vt`] mp_tac) >>
  simp[]
QED

Theorem build_getter_well_typed_HashMap_case[local]:
  !e kt typ vtyp n.
    (!args ret exp env container_vt.
       build_getter
         (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
            (Name kt (num_to_dec_string n)))
         typ vtyp (SUC n) = (args,ret,exp) /\
       type_place_expr env
         (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
            (Name kt (num_to_dec_string n))) = SOME container_vt /\
       subscript_vtype container_vt typ = SOME vtyp /\
       check_value_type env.type_defs vtyp /\
       (!id ty. MEM (id,ty) args ==>
          FLOOKUP env.var_types id = SOME ty) ==>
       well_typed_expr env exp /\ expr_type exp = ret /\
       type_place_expr env exp = SOME (Type ret)) ==>
    !args ret exp env container_vt.
      build_getter e kt (HashMapT typ vtyp) n = (args,ret,exp) /\
      type_place_expr env e = SOME container_vt /\
      subscript_vtype container_vt kt = SOME (HashMapT typ vtyp) /\
      check_value_type env.type_defs (HashMapT typ vtyp) /\
      (!id ty. MEM (id,ty) args ==>
         FLOOKUP env.var_types id = SOME ty) ==>
      well_typed_expr env exp /\ expr_type exp = ret /\
      type_place_expr env exp = SOME (Type ret)
Proof
  rpt strip_tac >>
  qpat_x_assum `build_getter e kt (HashMapT typ vtyp) n = _` mp_tac >>
  simp[Once build_getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  `FLOOKUP env.var_types (num_to_dec_string n) = SOME kt` by
    (qpat_assum `!id ty. (_ \/ MEM (id,ty) args') ==> _`
       (qspecl_then [`num_to_dec_string n`,`kt`] mp_tac) >>
     simp[]) >>
  `!id ty. MEM (id,ty) args' ==>
     FLOOKUP env.var_types id = SOME ty` by
    (rpt strip_tac >>
     qpat_assum `!id ty. (_ \/ MEM (id,ty) args') ==> _`
       (qspecl_then [`id`,`ty`] mp_tac) >>
     simp[]) >>
  `type_place_expr env
       (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
          (Name kt (num_to_dec_string n))) = SOME (HashMapT typ vtyp) /\
   subscript_vtype (HashMapT typ vtyp) typ = SOME vtyp /\
   check_value_type env.type_defs vtyp` by
    (irule generated_hashmap_getter_transition >> simp[]) >>
  qpat_assum `!env' container_vt'. _ ==> _`
    (qspecl_then [`env`,`HashMapT typ vtyp`] mp_tac) >>
  simp[]
QED

Theorem build_getter_well_typed_Type_scalar_case[local]:
  !e kt vt n.
    ~is_ArrayT vt ==>
    !args ret exp env container_vt.
      build_getter e kt (Type vt) n = (args,ret,exp) /\
      type_place_expr env e = SOME container_vt /\
      subscript_vtype container_vt kt = SOME (Type vt) /\
      check_value_type env.type_defs (Type vt) /\
      (!id ty. MEM (id,ty) args ==>
         FLOOKUP env.var_types id = SOME ty) ==>
      well_typed_expr env exp /\ expr_type exp = ret /\
      type_place_expr env exp = SOME (Type ret)
Proof
  rpt strip_tac >>
  qpat_x_assum `build_getter e kt (Type vt) n = _` mp_tac >>
  simp[Once build_getter_def] >>
  rpt strip_tac >> gvs[] >>
  `well_typed_expr env
     (Subscript ret e (Name kt (num_to_dec_string n))) /\
   type_place_expr env
     (Subscript ret e (Name kt (num_to_dec_string n))) = SOME (Type ret)` by
    (irule generated_subscript_well_typed_Type >> simp[]) >>
  simp[expr_type_def]
QED
(* KEY LEMMA: generated getter expressions retain exact place/result typing. *)
Theorem build_getter_well_typed[local]:
  !e kt vt n args ret exp env container_vt.
    build_getter e kt vt n = (args,ret,exp) /\
    type_place_expr env e = SOME container_vt /\
    subscript_vtype container_vt kt = SOME vt /\
    check_value_type env.type_defs vt /\
    (!id ty. MEM (id,ty) args ==>
       FLOOKUP env.var_types id = SOME ty) ==>
    well_typed_expr env exp /\ expr_type exp = ret /\
    type_place_expr env exp = SOME (Type ret)
Proof
  ho_match_mp_tac build_getter_input_ind >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `is_ArrayT vt`
      >- (qpat_x_assum `!vn. _`
            (qspec_then `num_to_dec_string n` mp_tac) >>
          simp[] >> disch_then assume_tac >>
          ho_match_mp_tac build_getter_well_typed_Type_array_case >>
          conj_tac >- first_assum ACCEPT_TAC >>
          first_assum ACCEPT_TAC) >>
      ho_match_mp_tac build_getter_well_typed_Type_scalar_case >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!vn. _`
    (qspec_then `num_to_dec_string n` mp_tac) >>
  simp[] >> disch_then assume_tac >>
  ho_match_mp_tac build_getter_well_typed_HashMap_case >>
  first_assum ACCEPT_TAC
QED

Theorem array_public_getter_tuple_shape_exact[local]:
  is_ArrayT typ /\
  external_getter_tuple src (VariableDecl Public mut id typ init) =
    SOME (gm,gnr,args,dflts,ret,body) ==>
  gm = View /\ gnr = F /\ dflts = [] /\
  ?exp. build_getter (TopLevelName typ (src,id)) (BaseT (UintT 256))
          (Type (ArrayT_type typ)) 0 = (args,ret,exp) /\
        body = [Return (SOME exp)]
Proof
  rw[external_getter_tuple_def, getter_def] >>
  Cases_on `build_getter (TopLevelName typ (src,id)) (BaseT (UintT 256))
              (Type (ArrayT_type typ)) 0` >>
  Cases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem build_getter_args_all_distinct[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) ==>
    ALL_DISTINCT (MAP FST args)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[MEM_MAP] >>
  metis_tac[build_getter_args_no_current_name, PAIR]
QED

Theorem build_getter_ret_checked[local]:
  !e kt vt n args ret exp tenv.
    build_getter e kt vt n = (args,ret,exp) /\
    check_value_type tenv vt ==>
    check_value_type tenv (Type ret)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[] >>
  first_x_assum irule >>
  gvs[check_value_type_def] >>
  Cases_on `vt` >>
  gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
      assignable_type_def, well_formed_type_def]
QED

Theorem check_value_type_ArrayT_type[local]:
  is_ArrayT typ /\
  check_value_type tenv (Type typ) ==>
  check_value_type tenv (Type (ArrayT_type typ))
Proof
  Cases_on `typ` >>
  gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
      assignable_type_def, well_formed_type_def]
QED

Theorem function_entry_env_args_lookup_package[local]:
  ALL_DISTINCT (MAP FST args) ==>
  (!id ty. MEM (id,ty) args ==>
     FLOOKUP (function_entry_env art mods src args).var_types
       id = SOME ty /\
     FLOOKUP (function_entry_env art mods src args).var_assignable
       id = SOME T) /\
  (!n ty. FLOOKUP (function_entry_env art mods src args).var_types n = SOME ty ==>
     ?id. MEM (id,ty) args /\ n = id) /\
  (!n b. FLOOKUP (function_entry_env art mods src args).var_assignable n = SOME b ==>
     ?id ty. MEM (id,ty) args /\ n = id /\ b = T)
Proof
  rw[function_entry_env_def]
  >- metis_tac[FOLDL_extend_local_args_formal_lookup]
  >- metis_tac[FOLDL_extend_local_args_formal_lookup]
  >- (drule_all FOLDL_extend_local_args_var_types_range >>
      simp[artifact_env_def])
  >- (drule_all FOLDL_extend_local_args_var_assignable_range >>
      simp[artifact_env_def])
QED

Theorem build_getter_function_entry_typing_package[local]:
  build_getter e kt vt n = (args,ret,exp) ==>
  type_place_expr (function_entry_env art mods src args) e = SOME container_vt ==>
  subscript_vtype container_vt kt = SOME vt ==>
  check_value_type (type_env_all_modules mods) vt ==>
  ALL_DISTINCT (MAP FST args) /\
  (?env_after.
     type_stmts (function_entry_env art mods src args) ret
       [Return (SOME exp)] = SOME env_after) /\
  (!id ty. MEM (id,ty) args ==>
     FLOOKUP (function_entry_env art mods src args).var_types
       id = SOME ty /\
     FLOOKUP (function_entry_env art mods src args).var_assignable
       id = SOME T) /\
  (!m ty. FLOOKUP (function_entry_env art mods src args).var_types m = SOME ty ==>
     ?id. MEM (id,ty) args /\ m = id) /\
  (!m b. FLOOKUP (function_entry_env art mods src args).var_assignable m = SOME b ==>
     ?id ty. MEM (id,ty) args /\ m = id /\ b = T)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP FST args)` by
    metis_tac[build_getter_args_all_distinct] >>
  `(!id ty. MEM (id,ty) args ==>
       FLOOKUP (function_entry_env art mods src args).var_types
         id = SOME ty /\
       FLOOKUP (function_entry_env art mods src args).var_assignable
         id = SOME T) /\
   (!m ty. FLOOKUP (function_entry_env art mods src args).var_types m = SOME ty ==>
       ?id. MEM (id,ty) args /\ m = id) /\
   (!m b. FLOOKUP (function_entry_env art mods src args).var_assignable m = SOME b ==>
       ?id ty. MEM (id,ty) args /\ m = id /\ b = T)` by
    metis_tac[function_entry_env_args_lookup_package] >>
  `well_typed_expr (function_entry_env art mods src args) exp /\
   expr_type exp = ret` by
    (drule build_getter_well_typed >>
     disch_then (qspecl_then
       [`function_entry_env art mods src args`, `container_vt`] mp_tac) >>
     simp[function_entry_env_def, artifact_env_def,
          FOLDL_extend_local_args_static] >>
     metis_tac[]) >>
  `ret <> NoneT` by
    (drule_all build_getter_ret_checked >>
     simp[check_value_type_def] >>
     metis_tac[assignable_type_not_NoneT]) >>
  simp[type_stmt_def] >>
  metis_tac[]
QED

Theorem checked_public_getter_body_typing_package:
  check_contract F
    (layouts:(address # (storage_layout # storage_layout)) list)
    (addr:160 word) mods = SOME art ==>
  ALOOKUP mods src = SOME ts ==>
  module_allocated layouts addr src ts ==>
  MEM decl ts ==>
  is_public_getter_decl fn decl ==>
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) ==>
  ALL_DISTINCT (MAP FST args) /\
  (?env_after.
     type_stmts (function_entry_env art mods src args) ret body = SOME env_after) /\
  (!id ty. MEM (id,ty) args ==>
     FLOOKUP (function_entry_env art mods src args).var_types
       id = SOME ty /\
     FLOOKUP (function_entry_env art mods src args).var_assignable
       id = SOME T) /\
  (!n ty. FLOOKUP (function_entry_env art mods src args).var_types n = SOME ty ==>
     ?id. MEM (id,ty) args /\ n = id) /\
  (!n b. FLOOKUP (function_entry_env art mods src args).var_assignable n = SOME b ==>
     ?id ty. MEM (id,ty) args /\ n = id /\ b = T)
Proof
  Cases_on `decl` >>
  simp[is_public_getter_decl_def, external_getter_tuple_def] >>
  Cases_on `v` >>
  simp[is_public_getter_decl_def, external_getter_tuple_def] >>
  ntac 6 strip_tac
  >- (Cases_on `is_ArrayT t`
      >- (gvs[] >>
          `mut = View /\ nr = F /\ dflts = [] /\
           ?exp. build_getter (TopLevelName t (src,fn))
                   (BaseT (UintT 256)) (Type (ArrayT_type t)) 0 =
                   (args,ret,exp) /\ body = [Return (SOME exp)]` by
            (irule array_public_getter_tuple_shape_exact >> simp[] >>
             qexistsl [`o'`, `v0`] >>
             simp[external_getter_tuple_def]) >>
          gvs[] >>
          `FLOOKUP art.cta_toplevel_vtypes (src,fn) =
             SOME (Type t)` by
            metis_tac[allocated_toplevel_vtype_VariableDecl] >>
          `check_toplevel_decl mods art src
             (VariableDecl Public v0 fn t o')` by
            metis_tac[check_contract_toplevel_decl_MEM] >>
          `check_value_type (type_env_all_modules mods) (Type t)` by
            (Cases_on `v0` >>
             gvs[check_toplevel_decl_def, check_value_type_def]) >>
          `check_value_type (type_env_all_modules mods)
             (Type (ArrayT_type t))` by
            metis_tac[check_value_type_ArrayT_type] >>
          irule (SRULE [] build_getter_function_entry_typing_package) >>
          qexistsl [`Type t`, `TopLevelName t (src,fn)`,
                    `BaseT (UintT 256)`, `0`, `Type (ArrayT_type t)`] >>
          simp[function_entry_env_def, artifact_env_def,
               FOLDL_extend_local_args_static, well_typed_expr_def] >>
          Cases_on `t` >>
          gvs[is_ArrayT_def, ArrayT_type_def, subscript_vtype_def,
              vtype_annotation_ok_def]) >>
      gvs[] >>
      `FLOOKUP art.cta_toplevel_vtypes (src,fn) =
         SOME (Type ret)` by
        metis_tac[allocated_toplevel_vtype_VariableDecl] >>
      `check_toplevel_decl mods art src
         (VariableDecl Public v0 fn ret o')` by
        metis_tac[check_contract_toplevel_decl_MEM] >>
      `well_formed_type (type_env_all_modules mods) ret /\ ret <> NoneT` by
        (Cases_on `v0` >>
         gvs[check_toplevel_decl_def] >>
         metis_tac[assignable_type_well_formed,
                   assignable_type_not_NoneT]) >>
      simp[function_entry_env_def, artifact_env_def, type_stmt_def,
           well_typed_expr_def, vtype_annotation_ok_def, expr_type_def]) >>
  `external_getter_tuple src (HashMapDecl Public b s t v0 o') =
     SOME (mut,nr,args,dflts,ret,body)` by
    simp[external_getter_tuple_def] >>
  drule hashmap_public_getter_tuple_shape >>
  strip_tac >>
  gvs[] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,fn) =
     SOME (HashMapT t v0)` by
    metis_tac[allocated_toplevel_vtype_HashMapDecl] >>
  `check_toplevel_decl mods art src
     (HashMapDecl Public b fn t v0 o')` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `check_value_type (type_env_all_modules mods) v0` by
    gvs[check_toplevel_decl_def] >>
  `hashmap_key_type t` by
    gvs[check_toplevel_decl_def] >>
  irule (SRULE [] build_getter_function_entry_typing_package) >>
  qexistsl [`HashMapT t v0`, `TopLevelName NoneT (src,fn)`, `t`, `0`, `v0`] >>
  simp[function_entry_env_def, artifact_env_def,
       FOLDL_extend_local_args_static, well_typed_expr_def,
       subscript_vtype_def, vtype_annotation_ok_def]
QED

val () = export_theory();
