(* Frame one immutable binding, rather than the whole immutable store. *)
Theory whitelistForIterImmFrame
Ancestors
  vyperBareGlobalName vyperPlaceFrames vyperState vyperTypeSystem
  stmtSimForArrayFrame vyperStatePreservation
  vyperTypeInvariants vyperInterpreter vyperAST list finite_map alist

Theorem lookup_immutable_set_other:
  (src',name') <> (src,name) /\
  set_immutable cx src' name' tv v es = (r,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[set_immutable_def, get_address_immutables_def,
       set_address_immutables_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[lookup_immutable_def] >>
  Cases_on `src' = src` >>
  gvs[set_source_immutables_def, get_source_immutables_def, FLOOKUP_UPDATE,
      ALOOKUP_ADELKEY]
QED

Theorem lookup_immutable_write_other:
  write_place cx p v es = (r,es') /\
  (!src' name' path. p = ImmutablePlace src' name' path ==>
                      (src',name') <> (src,name)) ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p`
  >- (strip_tac >> drule write_storage_place_immutables >>
      simp[lookup_immutable_def])
  >- (strip_tac >> drule write_memory_place_immutables >>
      simp[lookup_immutable_def]) >>
  rename1 `write_place cx (ImmutablePlace other_src other_name path)` >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables other_src imms) other_name` >>
  simp[return_def, raise_def] >>
  rename1 `FLOOKUP _ _ = SOME tva` >>
  Cases_on `assign_subscripts (FST tva) (SND tva) path (Replace v)` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> irule lookup_immutable_set_other >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Relate the semantic immutable root to the syntactic write guard. *)
Theorem lookup_global_immutable_root:
  lookup_global cx src id es =
    (INL (PlaceR (ImmutablePlace other_src other_id path)),es') ==>
  other_src = src /\ other_id = id /\ path = []
Proof
  simp[lookup_global_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
       bind_def, lift_option_type_def, return_def, raise_def,
       get_immutables_def, get_address_immutables_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs(), bind_def, return_def, raise_def]
QED

Theorem extend_place_immutable_root:
  extend_place cx pv sb es =
    (INL (PlaceR (ImmutablePlace src id path)),es') ==>
  ?oldpath. pv = PlaceR (ImmutablePlace src id oldpath)
Proof
  Cases_on `pv` >> Cases_on `sb` >>
  simp[oneline extend_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[bind_def, return_def, raise_def, lift_sum_def,
      value_type_CASE_rator, place_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs(), extend_memory_place_def] >>
  Cases_on `tv` >>
  gvs[oneline extend_storage_place_def, vyperValueTheory.value_CASE_rator,
      bind_def, ignore_bind_def, check_def, assert_def,
      lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[return_def]
QED

Theorem immutable_place_access_root_attrs[local]:
  !target attrs. FST (place_access target attrs) = FST (place_access target [])
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> simp[place_access_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem eval_base_place_immutable_root:
  !target cx es src id path es'.
    eval_base_place cx target es =
      (INL (PlaceR (ImmutablePlace src id path)),es') ==>
    FST (place_access target []) = TopLevelNameTarget (src,id)
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
         place_access_def]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      drule lookup_global_immutable_root >> simp[place_access_def]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner _ = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule >> simp[place_access_def, immutable_place_access_root_attrs]
QED

Theorem eval_target_place_immutable_root:
  eval_target_place cx target es = (INL (ImmutablePlace src id path),es') ==>
  FST (place_access target []) = TopLevelNameTarget (src,id)
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[eval_base_place_immutable_root]
QED

Theorem typed_guarded_immutable_target_write:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  type_place_target env target = SOME vt /\
  ~place_contains target (TopLevelNameTarget (src,name)) /\
  eval_target_place cx target es = (INL p,es1) /\
  write_place cx p v es1 = (r,es2) ==>
  lookup_immutable cx es2 src name = lookup_immutable cx es1 src name
Proof
  rpt strip_tac >> irule lookup_immutable_write_other >>
  goal_assum (drule_at Any) >> rpt strip_tac >> gvs[] >>
  drule eval_target_place_immutable_root >> strip_tac >>
  drule_at (Pat `type_place_target env target`) typed_guarded_array_root >>
  simp[] >> metis_tac[]
QED
