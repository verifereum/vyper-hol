Theory sourceTypeProps
Ancestors
  sourceTypeDefs sourceTypeResolve sourceConstAST sourceConstEval
  sourceConstAnnotation vyperTypeSystem vyperAST integer list
Libs
  intLib

(* TOP-LEVEL: source_type_resolve_well_formed,
   source_type_resolve_bound_provenance, source_type_claim_is_only_a_check.
   Runtime wellformedness includes nominal declaration and aggregate slot-size
   checks, not just positive syntactic lengths. Provenance covers ALL nested
   source bounds, including keys/values and tuple members. *)

Definition source_type_bound_provenance_def:
  source_type_bound_provenance env (e,n) =
    (source_const_eval env e = SC_Value (SCV_Int (&n)) /\
     0 < n /\ n < 2 ** 256)
End

Definition source_type_resolution_ok_def:
  source_type_resolution_ok tenv env r =
    (well_formed_vtype tenv (source_type_vtype r) /\
     EVERY (source_type_bound_provenance env) (source_type_bounds r))
End

Theorem source_type_bind_success:
  source_type_bind result f = ST_Ok y <=>
  ?x. result = ST_Ok x /\ f x = ST_Ok y
Proof
  Cases_on `result` >> simp[source_type_bind_def]
QED

Theorem source_type_bound_result_success:
  source_type_bound_result outcome = ST_Ok n ==>
  outcome = SC_Value (SCV_Int (&n)) /\ 0 < n /\ n < 2 ** 256
Proof
  Cases_on `outcome` >> simp[source_type_bound_result_def] >>
  rename1 `source_type_bound_result (SC_Value v)` >>
  Cases_on `v` >> simp[source_type_bound_result_def] >>
  rw[] >> gvs[] >> intLib.ARITH_TAC
QED

Theorem source_type_bound_success:
  source_type_bound env e = ST_Ok n ==>
  source_type_bound_provenance env (e,n)
Proof
  rw[source_type_bound_def, source_type_bound_provenance_def] >>
  drule source_type_bound_result_success >> simp[]
QED

Theorem source_type_checked_success:
  source_type_checked tenv vt qs bounds = ST_Ok r ==>
  r = SourceTypeResolution vt qs bounds /\ well_formed_vtype tenv vt
Proof
  rw[source_type_checked_def] >> gvs[]
QED

Theorem source_type_checked_ok:
  EVERY (source_type_bound_provenance env) bounds /\
  source_type_checked tenv vt qs bounds = ST_Ok r ==>
  source_type_resolution_ok tenv env r
Proof
  rw[source_type_resolution_ok_def] >>
  drule source_type_checked_success >>
  simp[source_type_vtype_def, source_type_bounds_def]
QED

Theorem source_type_sized_ok:
  source_type_sized tenv env is_string e = ST_Ok r ==>
  source_type_resolution_ok tenv env r
Proof
  rw[source_type_sized_def, source_type_bind_success] >>
  drule source_type_bound_success >> strip_tac >>
  drule source_type_checked_success >> strip_tac >>
  gvs[source_type_resolution_ok_def, source_type_vtype_def, source_type_bounds_def]
QED

Theorem source_type_array_ok:
  source_type_resolution_ok tenv env child /\
  source_type_array tenv env dynamic e child = ST_Ok r ==>
  source_type_resolution_ok tenv env r
Proof
  rw[source_type_array_def, source_type_bind_success] >>
  drule source_type_bound_success >> strip_tac >>
  drule source_type_checked_success >> strip_tac >>
  gvs[source_type_resolution_ok_def, source_type_vtype_def, source_type_bounds_def]
QED

Theorem source_type_hashmap_ok:
  source_type_resolution_ok tenv env key /\
  source_type_resolution_ok tenv env value /\
  source_type_hashmap tenv key value = ST_Ok r ==>
  source_type_resolution_ok tenv env r
Proof
  rw[source_type_hashmap_def, source_type_bind_success] >>
  gvs[AllCaseEqs()] >> drule source_type_checked_success >> strip_tac >>
  gvs[source_type_resolution_ok_def, source_type_vtype_def, source_type_bounds_def]
QED

Theorem source_type_tuple_bounds_ok:
  EVERY (source_type_resolution_ok tenv env) children ==>
  EVERY (source_type_bound_provenance env)
    (FLAT (MAP source_type_bounds children))
Proof
  Induct_on `children` >>
  simp[source_type_resolution_ok_def]
QED

Theorem source_type_tuple_ok:
  EVERY (source_type_resolution_ok tenv env) children /\
  source_type_tuple tenv children = ST_Ok r ==>
  source_type_resolution_ok tenv env r
Proof
  rw[source_type_tuple_def, source_type_bind_success] >>
  gvs[] >> drule source_type_checked_success >> strip_tac >>
  gvs[source_type_resolution_ok_def, source_type_vtype_def, source_type_bounds_def] >>
  irule source_type_tuple_bounds_ok >> qexists_tac `tenv` >> simp[]
QED

Theorem source_type_qualifier_preserves_ok:
  source_type_resolution_ok tenv env child /\
  source_type_add_qualifier q child = ST_Ok r ==>
  source_type_resolution_ok tenv env r
Proof
  Cases_on `child` >>
  rw[source_type_add_qualifier_def] >>
  gvs[source_type_resolution_ok_def, source_type_vtype_def,
      source_type_bounds_def]
QED

Theorem source_type_resolve_list_ok:
  !annotations rs.
  EVERY (\a. !r. source_type_resolve tenv names env a = ST_Ok r ==>
    source_type_resolution_ok tenv env r) annotations /\
  source_type_resolve_list tenv names env annotations = ST_Ok rs ==>
  EVERY (source_type_resolution_ok tenv env) rs
Proof
  Induct >> rw[source_type_resolve_def, source_type_bind_success] >>
  simp[] >> metis_tac[]
QED

Theorem source_type_resolve_ok:
  (!annotation r.
    source_type_resolve tenv names env annotation = ST_Ok r ==>
    source_type_resolution_ok tenv env r) /\
  (!annotations rs.
    source_type_resolve_list tenv names env annotations = ST_Ok rs ==>
    EVERY (source_type_resolution_ok tenv env) rs)
Proof
  ho_match_mp_tac (source_type_resolve_ind
    |> Q.SPECL [`\tenv names env a. P a`, `\tenv names env xs. Q xs`]
    |> SIMP_RULE (srw_ss()) []) >>
  rw[source_type_resolve_def, source_type_require_constructor_def,
     source_type_bind_success] >>
  gvs[AllCaseEqs(), source_type_bind_success]
  >- (drule source_type_checked_success >> rw[] >>
      simp[source_type_resolution_ok_def, source_type_vtype_def,
           source_type_bounds_def])
  >- (drule source_type_sized_ok >> simp[])
  >- (drule source_type_sized_ok >> simp[])
  >- metis_tac[source_type_array_ok]
  >- metis_tac[source_type_array_ok]
  >- metis_tac[source_type_hashmap_ok]
  >- metis_tac[source_type_tuple_ok]
  >- metis_tac[source_type_qualifier_preserves_ok]
QED

Theorem source_type_resolve_well_formed:
  source_type_resolve tenv names env annotation = ST_Ok r ==>
  well_formed_vtype tenv (source_type_vtype r)
Proof
  metis_tac[source_type_resolve_ok, source_type_resolution_ok_def]
QED

Theorem source_type_resolve_bound_provenance:
  source_type_resolve tenv names env annotation = ST_Ok r /\
  MEM (e,n) (source_type_bounds r) ==>
  source_const_eval env e = SC_Value (SCV_Int (&n)) /\
  0 < n /\ n < 2 ** 256
Proof
  strip_tac >> drule (CONJUNCT1 source_type_resolve_ok) >>
  simp[source_type_resolution_ok_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `(e,n)` mp_tac) >>
  simp[source_type_bound_provenance_def]
QED

Theorem source_type_resolve_runtime_well_formed:
  source_type_resolve tenv names env annotation = ST_Ok r /\
  source_type_vtype r = Type ty ==>
  well_formed_type tenv ty
Proof
  metis_tac[source_type_resolve_well_formed, well_formed_vtype_def]
QED

Theorem source_type_claim_is_only_a_check:
  source_type_check_claim tenv names env annotation claim = ST_Ok r <=>
  source_type_resolve tenv names env annotation = ST_Ok r /\
  source_type_vtype r = claim
Proof
  rw[source_type_check_claim_def, source_type_bind_success] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem source_type_name_not_spelling:
  ALOOKUP names path = NONE ==>
  source_type_resolve tenv names env (SCA_Name path) =
    ST_Error (STE_Unresolved path)
Proof
  simp[source_type_resolve_def, source_type_name_def, source_type_bind_def]
QED
