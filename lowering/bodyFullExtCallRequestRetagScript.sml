(* Nonmemory external-call argument retagging retains its interpretation. *)
Theory bodyFullExtCallRequestRetag
Ancestors
  exprPtrUnwrapStorageShape bodyPtrDefs loweringPosts exprLowering

Theorem extcall_nonmemory_retag:
  compile_expr ce ty e sa = (LocatedValue tag p,sm) /\
  p.ptr_location <> LocMemory /\
  vv_holds ce cx (post_value_type ce e) tv (LocatedValue tag p) ee s /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue tag p) ee G tn s ==>
  vv_holds ce cx (lowered_value_type ce e) tv
    (ext_call_arg_value (lowered_value_type ce e) (LocatedValue tag p)) ee s /\
  ptr_vv_ok cx (lowered_value_type ce e) tv
    (ext_call_arg_value (lowered_value_type ce e) (LocatedValue tag p)) ee G tn s
Proof
  strip_tac >> drule_all compile_nonmemory_lowered_value_type >> strip_tac >>
  drule post_value_type_lowered >> strip_tac >>
  gvs[ext_call_arg_value_def, vv_holds_def, ptr_vv_ok_def]
QED
