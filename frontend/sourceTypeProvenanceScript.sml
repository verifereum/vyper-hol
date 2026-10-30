Theory sourceTypeProvenance
Ancestors
  sourceTypeDefs sourceTypeResolve sourceTypeProps sourceConstAnnotation list

(* TOP-LEVEL: source_type_resolve_original_bounds. Together with
   source_type_resolve_bound_provenance this proves that ALL original source
   bounds occur, in structural left-to-right/postorder, with exact mathematical
   values. No inferred/folded bound can be substituted or omitted. *)
Definition source_type_annotation_bounds_def:
  source_type_annotation_bounds (SCA_Name path) = [] /\
  source_type_annotation_bounds (SCA_String e) = [e] /\
  source_type_annotation_bounds (SCA_Bytes e) = [e] /\
  source_type_annotation_bounds (SCA_StaticArray a e) =
    source_type_annotation_bounds a ++ [e] /\
  source_type_annotation_bounds (SCA_DynArray a e) =
    source_type_annotation_bounds a ++ [e] /\
  source_type_annotation_bounds (SCA_HashMap k v) =
    source_type_annotation_bounds k ++ source_type_annotation_bounds v /\
  source_type_annotation_bounds (SCA_Tuple annotations) =
    FLAT (MAP source_type_annotation_bounds annotations) /\
  source_type_annotation_bounds (SCA_Qualified q a) = source_type_annotation_bounds a
End

Theorem source_type_sized_bound_sources:
  source_type_sized tenv env is_string e = ST_Ok r ==>
  MAP FST (source_type_bounds r) = [e]
Proof
  rw[source_type_sized_def, source_type_bind_success] >>
  drule source_type_checked_success >> rw[] >> simp[source_type_bounds_def]
QED

Theorem source_type_array_bound_sources:
  source_type_array tenv env dynamic e child = ST_Ok r ==>
  MAP FST (source_type_bounds r) = MAP FST (source_type_bounds child) ++ [e]
Proof
  rw[source_type_array_def, source_type_bind_success] >>
  drule source_type_checked_success >> rw[] >> simp[source_type_bounds_def]
QED

Theorem source_type_hashmap_bound_sources:
  source_type_hashmap tenv key value = ST_Ok r ==>
  MAP FST (source_type_bounds r) =
  MAP FST (source_type_bounds key) ++ MAP FST (source_type_bounds value)
Proof
  rw[source_type_hashmap_def, source_type_bind_success] >>
  gvs[AllCaseEqs()] >> drule source_type_checked_success >> rw[] >>
  simp[source_type_bounds_def]
QED

Theorem source_type_tuple_bound_sources:
  source_type_tuple tenv children = ST_Ok r ==>
  MAP FST (source_type_bounds r) =
  FLAT (MAP (\child. MAP FST (source_type_bounds child)) children)
Proof
  rw[source_type_tuple_def, source_type_bind_success] >>
  gvs[] >> drule source_type_checked_success >> rw[] >>
  simp[source_type_bounds_def, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem source_type_qualifier_bound_sources:
  source_type_add_qualifier q child = ST_Ok r ==>
  source_type_bounds r = source_type_bounds child
Proof
  Cases_on `child` >> rw[source_type_add_qualifier_def] >>
  gvs[source_type_bounds_def]
QED

Theorem source_type_resolve_original_bounds:
  (!annotation r.
    source_type_resolve tenv names env annotation = ST_Ok r ==>
    MAP FST (source_type_bounds r) = source_type_annotation_bounds annotation) /\
  (!annotations rs.
    source_type_resolve_list tenv names env annotations = ST_Ok rs ==>
    MAP (\r. MAP FST (source_type_bounds r)) rs =
    MAP source_type_annotation_bounds annotations)
Proof
  ho_match_mp_tac (source_type_resolve_ind
    |> Q.SPECL [`\tenv names env a. P a`, `\tenv names env xs. Q xs`]
    |> SIMP_RULE (srw_ss()) []) >>
  rw[source_type_resolve_def, source_type_require_constructor_def,
     source_type_annotation_bounds_def, source_type_bind_success] >>
  gvs[AllCaseEqs(), source_type_bind_success]
  >- (drule source_type_checked_success >> rw[] >> simp[source_type_bounds_def])
  >- (drule source_type_sized_bound_sources >> simp[])
  >- (drule source_type_sized_bound_sources >> simp[])
  >- metis_tac[source_type_array_bound_sources]
  >- metis_tac[source_type_array_bound_sources]
  >- metis_tac[source_type_hashmap_bound_sources]
  >- metis_tac[source_type_tuple_bound_sources]
  >- metis_tac[source_type_qualifier_bound_sources]
QED
