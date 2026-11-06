Theory bodyPtrIfExpCallTag
Ancestors bodyPtrIfExpLocatedTag bodyPtrIfExpCallShape bodyPtrIfExpUnwrapContract

(* Local normal-post incompatibility, not an operand or target counterexample. *)
Theorem ifexp_buffer_call_post_incompatible:
  compile_call cfn cenv ret_ty ty (IntCall func_id) args dret st = (v,st') /\
  cenv.ce_func_info (nsid_to_string func_id) = (0,rbs,pvs) /\ 0 < rbs /\
  cenv.ce_func_return_type (nsid_to_string func_id) <> expr_type e ==>
  ~vv_post ctx func cenv cx e es sa sb s0 ee tv v t
Proof
  strip_tac >> drule_all compile_call_intcall_buffer_shape >> strip_tac >>
  gvs[] >> strip_tac >> drule vv_post_located_type >> simp[]
QED
