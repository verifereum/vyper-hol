(* An effect-free expression's ordinary value post already gives its
   internal-call argument provenance, unless its value is in code or its
   type contains a dynamic array. *)
Theory bodyIntCallPostProvenance
Ancestors
  bodyIntCallProducerInterface bodyIntCallArgType loweringPosts

Theorem vv_post_intcall_provenance:
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
  ~expr_has_effect e /\
  (!t' p. vv = LocatedValue t' p ==> p.ptr_location <> LocCode) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
         dynarray_free tvt) ==>
  intcall_vv_provenance cenv cx (expr_type e) sa sb ee tv vv t
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[effect_free_post_value_type] >>
  gvs[vv_post_def, intcall_vv_provenance_def] >>
  Cases_on `vv` >> gvs[vv_at_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> gvs[] >> metis_tac[]
QED
