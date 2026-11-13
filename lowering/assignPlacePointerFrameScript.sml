(* Existing local pointers need only forward preservation of defined variables. *)
Theory assignPlacePointerFrame
Ancestors loweringPosts exprLoweringProps context compileEnv

Theorem assign_place_ptr_rel_forward_frame:
  !cenv cx s u sa pv w loc vt.
    place_ptr_rel cenv cx s pv w loc vt /\ local_ptrs_reserved cenv sa /\
    (!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==>
           lookup_var x u = SOME z) ==>
    place_ptr_rel cenv cx u pv w loc vt
Proof
  rpt gen_tac >> Cases_on `pv` >> simp[place_ptr_rel_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> simp[place_ptr_rel_def] >>
  rpt strip_tac >> gvs[] >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  metis_tac[]
QED
