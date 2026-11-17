Theory bodyAssignRepresentationLive
Ancestors
  loweringPosts vyperTypeInvariants vyperState vyperTypeEnv vyperValue
  vyperContext vyperAST

Theorem body_assign_representation_storage_live:
  env.type_defs = get_tenv cx /\
  eval_result_typed (env,cx,es1) pv (Type ty) /\
  vv_place_ptr cenv cx es1 s pv vv /\
  (!t p. vv = LocatedValue t p /\
     (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
     t = ty /\ (!v. pv <> Value v)) /\
  (!tr slot leaf. pv = PlaceR (StoragePlace tr slot leaf) ==>
     storage_read_live H tr (get_storage cx es1 tr) slot leaf) ==>
  vv_storage_live H cx vv es1 s
Proof
  Cases_on `vv` >- simp[] >>
  rpt strip_tac >>
  rename1 `vv_place_ptr cenv cx es1 s pv (LocatedValue t p)` >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (first_x_assum (qspecl_then [`t`, `p`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `pv` >> gvs[eval_result_typed_def] >>
      Cases_on `p'` >>
      gvs[vv_place_ptr_def, runtime_place_typed_def, place_type_value_def,
          slot_loc_def, vyperStateTheory.return_def] >>
      Cases_on `b` >> gvs[]) >>
  gvs[]
QED
