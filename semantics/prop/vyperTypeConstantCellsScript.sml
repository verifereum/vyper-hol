(* Declaration typing for constant cells stored in immutable tables. *)
Theory vyperTypeConstantCells
Ancestors
  list rich_list finite_map alist option pair
  vyperAST vyperValue vyperState vyperContext vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants
  vyperTypeContractStaticMaps vyperTypeInitialState

Theorem module_toplevel_vtype_key_MEM_Variable_any:
  MEM (VariableDecl vis mut id ty init) ts ==>
  MEM (src,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,id)]` >> simp[] >>
  qexists `VariableDecl vis mut id ty init` >>
  simp[toplevel_vtype_keys_toplevel_def]
QED

Theorem module_immutable_constant_names_distinct:
  !src ts visI idI tyI initI visC e idC tyC slotC.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visC (Constant e) idC tyC slotC) ts ==>
    idI <> idC
Proof
  gen_tac >> Induct_on `ts` >- simp[] >> rpt gen_tac >>
  Cases_on `h` >>
  simp[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED

Theorem module_constant_name_type_unique:
  !src ts visI eI idI tyI initI visJ eJ idJ tyJ initJ.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI (Constant eI) idI tyI initI) ts /\
    MEM (VariableDecl visJ (Constant eJ) idJ tyJ initJ) ts /\
    idJ = idI ==> tyJ = tyI
Proof
  gen_tac >> Induct_on `ts` >- simp[] >> rpt gen_tac >>
  Cases_on `h` >>
  simp[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED

Theorem initial_immutables_module_lookup_origin:
  !tenv init_src ts acc imms query_src id tv v.
  initial_immutables_module tenv init_src ts acc = SOME imms /\
  FLOOKUP (get_source_immutables query_src imms) id = SOME (tv,v) ==>
  FLOOKUP (get_source_immutables query_src acc) id = SOME (tv,v) \/
  init_src = query_src /\
  ?vis id_str ty init.
    MEM (VariableDecl vis Immutable id_str ty init) ts /\
    id_str = id /\ evaluate_type tenv ty = SOME tv
Proof
  recInduct initial_immutables_module_ind >>
  rw[initial_immutables_module_def] >> gvs[AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  Cases_on `src_id_opt = query_src` >>
  gvs[update_immutable_def, get_source_immutables_set_same,
      get_source_immutables_set_other, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >>
  gvs[update_immutable_def, get_source_immutables_set_same,
      FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem initial_immutables_lookup_origin:
  !tenv mods imms src id tv v.
  initial_immutables tenv mods = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
  ?ts vis id_str ty init.
    MEM (src,ts) mods /\
    MEM (VariableDecl vis Immutable id_str ty init) ts /\
    id_str = id /\ evaluate_type tenv ty = SOME tv
Proof
  gen_tac >> Induct_on `mods`
  >- simp[initial_immutables_def, empty_immutables_def,
          get_source_immutables_def] >>
  rpt gen_tac >> PairCases_on `h` >> rw[initial_immutables_def] >>
  gvs[AllCaseEqs()] >>
  drule initial_immutables_module_lookup_origin >> disch_then drule >>
  strip_tac
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl [`ts`,`vis`,`ty`,`init`] >> gvs[]) >>
  qexistsl [`h1`,`vis`,`ty`,`init`] >> gvs[]
QED

Definition deployment_constant_cells_typed_def:
  deployment_constant_cells_typed tenv addr mods (am:abstract_machine) <=>
    !src ts vis e id ty init tv v.
      MEM (src,ts) mods /\
      MEM (VariableDecl vis (Constant e) id ty init) ts /\
      FLOOKUP (get_source_immutables src
        (case ALOOKUP am.immutables addr of
         | SOME imms => imms | NONE => [])) id = SOME (tv,v) ==>
      evaluate_type tenv ty = SOME tv /\ value_has_type tv v
End

Theorem deployment_constant_cells_typed_lookup:
  deployment_constant_cells_typed tenv addr mods am /\
  MEM (src,ts) mods /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of
     | SOME imms => imms | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v
Proof
  metis_tac[deployment_constant_cells_typed_def]
QED

Definition constant_fmap_declared_typed_def:
  constant_fmap_declared_typed tenv ts
      (m : (string, type_value # value) fmap) <=>
    !id tv v. FLOOKUP m id = SOME (tv,v) ==>
      ?vis e id_str ty init.
        MEM (VariableDecl vis (Constant e) id_str ty init) ts /\
        id_str = id /\
        evaluate_type tenv ty = SOME tv /\ value_has_type tv v
End

Theorem constant_fmap_declared_typed_lookup:
  constant_fmap_declared_typed tenv ts m /\
  FLOOKUP m id = SOME (tv,v) ==>
  ?vis e id_str ty init.
    MEM (VariableDecl vis (Constant e) id_str ty init) ts /\
    id_str = id /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v
Proof
  metis_tac[constant_fmap_declared_typed_def]
QED

Theorem checked_initial_immutables_constant_absent:
  check_contract mode layouts addr mods = SOME artifact /\
  initial_immutables tenv mods = SOME imms /\
  MEM (src,ts) mods /\
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  FLOOKUP (get_source_immutables src imms) id = NONE
Proof
  strip_tac >>
  `contract_namespaces_ok F mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     Cases_on `mode` >> simp[check_contract_def] >>
     metis_tac[contract_namespaces_ok_deploy_implies_runtime]) >>
  Cases_on `FLOOKUP (get_source_immutables src imms) id` >> simp[] >>
  PairCases_on `x` >>
  drule_all initial_immutables_lookup_origin >> strip_tac >> gvs[] >>
  `ts' = ts` by
    ( `ALOOKUP mods src = SOME ts` by
        (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[contract_namespaces_ok_def]) >>
      `ALOOKUP mods src = SOME ts'` by
        (irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[contract_namespaces_ok_def]) >>
      gvs[]) >> gvs[] >>
  metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys,
            module_immutable_constant_names_distinct]
QED

Theorem merge_constants_preserves_constant_cells_typed:
  contract_namespaces_ok F mods /\ ALOOKUP mods src = SOME ts /\
  deployment_constant_cells_typed tenv addr mods am /\
  constant_fmap_declared_typed tenv ts cenv ==>
  deployment_constant_cells_typed tenv addr mods
    (merge_constants addr src cenv am)
Proof
  strip_tac >>
  simp[deployment_constant_cells_typed_def, merge_constants_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `src' = src` >>
  gvs[get_source_immutables_set_same, get_source_immutables_set_other,
      FLOOKUP_FUNION]
  >- (Cases_on `FLOOKUP cenv id` >> gvs[]
      >- (gvs[empty_immutables_def] >>
          drule_all deployment_constant_cells_typed_lookup >> simp[]) >>
      drule_all constant_fmap_declared_typed_lookup >> strip_tac >>
      `ts' = ts` by
        (`ALOOKUP mods src = SOME ts'` by
           (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
            gvs[contract_namespaces_ok_def]) >> gvs[]) >>
      gvs[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys] >>
      `ty' = ty` by metis_tac[module_constant_name_type_unique] >>
      gvs[]) >>
  gvs[empty_immutables_def] >>
  drule_all deployment_constant_cells_typed_lookup >> simp[]
QED

Theorem constant_fmap_declared_typed_empty[simp]:
  constant_fmap_declared_typed tenv ts FEMPTY
Proof
  simp[constant_fmap_declared_typed_def]
QED

Theorem constant_fmap_declared_typed_update:
  constant_fmap_declared_typed tenv ts m /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  constant_fmap_declared_typed tenv ts (m |+ (id,(tv,v)))
Proof
  rw[constant_fmap_declared_typed_def, FLOOKUP_UPDATE] >>
  Cases_on `id' = id` >> gvs[] >> metis_tac[]
QED

Theorem checked_constant_declared_type:
  check_contract mode (checker_layouts : ('checker_addr, ((num option # string), 'checker_slot) alist # ((num option # string), 'checker_slot) alist) alist) checker_addr mods = SOME artifact /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  MEM (src,ts) mods /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  well_typed_expr (artifact_env artifact mods current_src)
    (TopLevelName ann (src,id)) ==>
  ann = ty
Proof
  strip_tac >>
  `contract_namespaces_ok F mods` by
    metis_tac[check_contract_runtime_namespaces] >>
  `ALOOKUP mods src = SOME ts` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  `FLOOKUP artifact.cta_toplevel_vtypes (src,id) = SOME (Type ty)` by
    (irule check_contract_bare_global_toplevel_vtype >> metis_tac[]) >>
  gvs[well_typed_expr_def, artifact_env_def] >>
  drule check_contract_bare_globals_consistent_checked >>
  disch_then (qspecl_then [`cx.txn`,`cx.sources`,`cx.layouts`] mp_tac) >> simp[] >>
  disch_then (qspec_then `src` mp_tac) >>
  disch_then (qspecl_then [`id`,`ann`] mp_tac) >> simp[] >>
  metis_tac[]
QED
