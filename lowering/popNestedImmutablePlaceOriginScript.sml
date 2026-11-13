(* Immutable root provenance for the evaluator's write-access analysis. *)
Theory popNestedImmutablePlaceOrigin
Ancestors
  vyperLocalAccessFrame vyperStoragePlaceProvenance
  vyperSubscriptOverlap vyperInterpreter vyperState vyperMisc
  list alist finite_map

Theorem extend_place_immutable_origin[local]:
  extend_place cx r sb s = (INL (PlaceR (ImmutablePlace src id path)),t) ==>
  ?path0. r = PlaceR (ImmutablePlace src id path0)
Proof
  Cases_on `r` >> simp[extend_place_def, raise_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, extend_memory_place_def, bind_def,
           ignore_bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule extend_storage_place_subregion >> simp[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[value_type_CASE_rator, return_def, raise_def, bind_def, AllCaseEqs()]
QED

Theorem lookup_global_immutable_origin[local]:
  lookup_global cx src0 id0 s =
    (INL (PlaceR (ImmutablePlace src id path)),t) ==>
  src0 = src /\ id0 = id
Proof
  simp[lookup_global_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
       bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_base_place_immutable_access:
  !bt cx s src id path t.
  eval_base_place cx bt s =
    (INL (PlaceR (ImmutablePlace src id path)),t) ==>
  MEM (WriteAcc (StateRef (src,id))) (accesses_target bt)
Proof
  measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def,
           type_check_def, assert_def, ignore_bind_def, return_def, raise_def,
           accesses_expr_def, AllCaseEqs()]
  >- (PairCases_on `p` >> simp[Once evaluate_def, accesses_expr_def] >>
      metis_tac[lookup_global_immutable_origin])
  >- (simp[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def] >>
      rpt strip_tac >> drule extend_place_immutable_origin >>
      strip_tac >> gvs[] >> first_x_assum (qspec_then `b` mp_tac) >>
      simp[] >> metis_tac[]) >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), accesses_expr_def] >>
  rpt strip_tac >> drule extend_place_immutable_origin >>
  strip_tac >> gvs[] >> first_x_assum (qspec_then `b` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem eval_target_place_immutable_access:
  eval_target_place cx bt s = (INL (ImmutablePlace src id path),t) ==>
  MEM (WriteAcc (StateRef (src,id))) (accesses_target bt)
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[eval_base_place_immutable_access]
QED
