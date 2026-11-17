(* Temporary worker: storage roots and Pop source constructors. *)
Theory bodyAssignStorageBaseOrigin
Ancestors
  bodySim exprLowering context compileEnv compileVyper entryStateRel bodyStorageMetadata
  bodyAugPlaceTarget targetPlaceSim vyperTypeContractStaticMaps
  vyperInterpreter vyperState vyperAST finite_map list pair
  vyperPlaceMutationSoundness exprSimPopNestedBase

Theorem body_assign_module_storage_decl[local]:
  body_inv tops ctx cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME ml /\
  ((?slot. ml = StorageLoc slot) \/ (?slot. ml = TransientLoc slot)) ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE
Proof
  strip_tac >>
  `cenv_module_pins tops cenv /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))`
    by fs[body_inv_def] >>
  gvs[cenv_module_pins_def] >>
  drule add_immutable_locations_FLOOKUP >> simp[] >> strip_tac >>
  drule add_module_var_locations_cases >> simp[] >> strip_tac >> gvs[]
  >>~- ([`MEM (VariableDecl _ _ _ _ _) _`],
         drule bodyStorageMetadataTheory.find_var_decl_storage_some >> simp[]) >>
  drule_all find_var_decl_by_name_SOME_hashmap >> simp[]
QED

Theorem body_assign_storage_target_root[local]:
  !bt f cenv sa op loc pt sb tops ctx cx.
    body_inv tops ctx cenv cx /\
    compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
    (loc = LocStorage \/ loc = LocTransient) ==>
    ~immutable_root cx bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt`
  >- simp[immutable_root_def, target_root_def]
  >- (PairCases_on `p` >> rpt gen_tac >>
      simp[compile_get_target_ptr_def, LET_THM] >>
      rpt BasicProvers.TOP_CASE_TAC >> simp[comp_return_def] >>
      rpt strip_tac >> gvs[] >>
      `p0 = NONE /\ find_var_decl_by_name p1 tops <> NONE` by
        (irule body_assign_module_storage_decl >> metis_tac[]) >>
      gvs[immutable_root_def, target_root_def] >>
      `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >> gvs[]) >>
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  rpt BasicProvers.TOP_CASE_TAC >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  PairCases_on `result` >> gvs[] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  metis_tac[immutable_root_def, target_root_def]
QED

Theorem body_assign_storage_target_not_immutable:
  body_inv tops ctx cenv cx /\
  compile_get_target_ptr f cenv bt sa = ((op,SOME loc,pt),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_target_place cx bt es = (INL p,es1) ==>
  !src id path. p <> ImmutablePlace src id path
Proof
  strip_tac >>
  `~immutable_root cx bt` by (irule body_assign_storage_target_root >> metis_tac[]) >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[aug_place_base_immutable_origin]
QED

Theorem body_assign_pop_nonvalue[local]:
  (!src id path. p <> ImmutablePlace src id path) /\
  pop_place cx p es = (INL pv,es1) ==> !v. pv <> Value v
Proof
  Cases_on `p` >> simp[] >> strip_tac
  >~ [`pop_place _ (MemoryPlace _ _) _ = _`]
  >- (drule vyperPlaceMutationSoundnessTheory.pop_memory_place_success >>
      strip_tac >> gvs[]) >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  Cases_on `t` >> simp[pop_place_def, raise_def] >>
  rename1 `ArrayTV _ bd` >> Cases_on `bd` >>
  simp[pop_place_def, raise_def, bind_def, ignore_bind_def,
       return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem body_assign_storage_base_result:
  body_inv tops ctx cenv cx /\
  (case e of TopLevelName _ _ => T | Pop _ _ => T | _ => F) /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  eval_expr cx e es = (INL pv,es1) ==>
  t = expr_type e /\ (!v. pv <> Value v)
Proof
  Cases_on `e` >> simp[]
  >- (PairCases_on `p'` >> strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars (p'0,p'1)` >>
      gvs[] >> rpt BasicProvers.TOP_CASE_TAC >>
      rpt (pairarg_tac >> gvs[]) >> disch_tac >> gvs[mk_ptr_def] >>
      `p'0 = NONE /\ find_var_decl_by_name p'1 tops <> NONE` by
        (irule body_assign_module_storage_decl >> metis_tac[]) >>
      `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, lookup_global_def] >>
      Cases_on `find_var_decl_by_name p'1 tops` >> gvs[] >>
      PairCases_on `x` >> Cases_on `x0` >>
      simp[bind_def, ignore_bind_def, lift_option_type_def,
           return_def, raise_def, record_storage_event_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (strip_tac >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      rewrite_tac[nested_pop_compile_eq] >> simp[LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `loc_opt` >> simp[mk_ptr_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      `!src id path. p <> ImmutablePlace src id path` by
        (irule body_assign_storage_target_not_immutable >> metis_tac[]) >>
      simp[expr_type_def] >> irule body_assign_pop_nonvalue >> metis_tac[])
QED
