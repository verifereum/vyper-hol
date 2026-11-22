(* A successful guarded target retains its syntactic root at every path. *)
Theory vyperGuardedCellMutations
Ancestors
  vyperRuntimeWriteSafety vyperProtectedImmutableFrame
  vyperStoragePlaceProvenance vyperBareGlobalName vyperPlaceFrames
  vyperScopePreservation vyperStatePreservation vyperCallOutcomeFrame
  vyperInterpreter vyperState vyperAST pair

Theorem guarded_base_place_immutable_origin[local]:
  !t cx st src id path st'.
    runtime_write_root R t /\
    eval_base_place cx t st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
    R src id /\
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  measureInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >> rpt gen_tac >> strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- (drule eval_name_target_memory_root >> simp[])
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget root) st = _` >>
      PairCases_on `root` >> gvs[Once evaluate_def, runtime_write_root_def] >>
      drule lookup_global_immutable_root >> strip_tac >> gvs[] >>
      gvs[lookup_global_def, vyperMiscTheory.option_CASE_rator,
          vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator, bind_def,
          lift_option_type_def, return_def, raise_def, get_immutables_def,
          get_address_immutables_def, AllCaseEqs(), ignore_bind_def,
          record_storage_event_def]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def,
      runtime_write_root_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner _ = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem guarded_base_place_root[local]:
  !t cx st src id path st'.
    runtime_write_root R t /\
    eval_base_place cx t st = (INL (PlaceR (ImmutablePlace src id path)),st') ==>
    R src id
Proof
  metis_tac[guarded_base_place_immutable_origin]
QED

Theorem guarded_target_place_root[local]:
  runtime_write_root R tgt /\
  eval_target_place cx tgt st = (INL (ImmutablePlace src id path),mid) ==>
  R src id
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[guarded_base_place_root]
QED

Theorem runtime_resolved_target_not_immutable:
  runtime_write_roots_resolve cx R /\ runtime_write_root R tgt /\
  eval_target_place cx tgt st = (INL pl,mid) ==>
  !sid id path. pl <> ImmutablePlace sid id path
Proof
  rpt strip_tac >> gvs[] >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all guarded_base_place_immutable_origin >> strip_tac >>
  fs[runtime_write_roots_resolve_def] >> res_tac >> gvs[]
QED

Theorem runtime_guarded_cell_mutations:
  runtime_write_root (\s id. (s,id) <> (sid,nm)) tgt /\
  eval_target_place cx tgt st = (INL pl,mid) ==>
  (!v. state_rel_frame
         (\s t. lookup_immutable cx t sid nm = lookup_immutable cx s sid nm)
         (write_place cx pl v)) /\
  (!v. state_rel_frame
         (\s t. lookup_immutable cx t sid nm = lookup_immutable cx s sid nm)
         (append_place cx pl v)) /\
  state_rel_frame
    (\s t. lookup_immutable cx t sid nm = lookup_immutable cx s sid nm)
    (pop_place cx pl)
Proof
  strip_tac >>
  `!src id path. pl = ImmutablePlace src id path ==> (src,id) <> (sid,nm)` by
    (rpt strip_tac >> gvs[] >> drule_all guarded_target_place_root >> simp[]) >>
  simp[state_rel_frame_result] >> rpt conj_tac >> rpt gen_tac >> disch_tac
  >- metis_tac[lookup_immutable_write_other]
  >- (Cases_on `pl` >> gvs[]
      >~ [`append_place _ (StoragePlace _ _ _) _ _ = _`]
      >- (drule append_storage_place_scopes_immutables >> simp[lookup_immutable_def]) >>
      gvs[append_place_def, bind_def, AllCaseEqs()] >>
      imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
      imp_res_tac lift_sum_state >> gvs[] >>
      irule lookup_immutable_write_other >> goal_assum (drule_at Any) >> simp[])
  >- metis_tac[pop_place_immutable_other]
QED
