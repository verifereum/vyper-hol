(* Value-post type information used at internal-call staging. *)
Theory bodyIntCallArgType
Ancestors
  loweringPosts

Theorem effect_free_post_value_type:
  ~expr_has_effect e ==> post_value_type ce e = expr_type e
Proof
  strip_tac >> irule post_value_type_not_int_call >>
  rpt strip_tac >> gvs[]
QED

Theorem vv_holds_located_type:
  vv_holds ce cx ty raw (LocatedValue sty p) es s ==>
  sty = ty \/
  p.ptr_location = LocMemory /\ is_bytestring_type ty /\
  is_bytestring_type sty
Proof
  simp[vv_holds_def] >> metis_tac[]
QED
