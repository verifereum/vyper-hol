(* Memory retagging changes interpretation, not the buffer or its site. *)
Theory bodyFullExtCallRequestSnapshotMemory
Ancestors
  bodyFullExtCallRequestSnapshotWord bodyPtrIfExpMemoryTransport
  abiEncodeMaterialize valueCopyBytes bodyPtrDefs loweringPosts exprSimHyps

Theorem extcall_request_bytestring_memory_retag[local]:
  p.ptr_location = LocMemory /\
  is_bytestring_type src /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  value_has_type sv v /\ value_has_type dv v /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx src raw (LocatedValue tag p) ee s /\
  ptr_vv_ok cx src raw (LocatedValue tag p) ee G tn s ==>
  vv_holds ce cx dst raw (LocatedValue dst p) ee s /\
  ptr_vv_ok cx dst raw (LocatedValue dst p) ee G tn s
Proof
  strip_tac >>
  `ptr_mem_ok cx dst v p.ptr_operand G tn s` by
    (gvs[ptr_vv_ok_def] >> metis_tac[ptr_mem_ok_bytestring_transport]) >>
  `~is_word_type dst` by metis_tac[is_bytestring_word_type] >>
  gvs[vv_holds_def, ptr_vv_ok_def] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED

Theorem extcall_request_memory_retag:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  ~is_word_type (expr_type e) /\
  compile_expr ce (expr_type e) e sa = (LocatedValue tag p,sm) /\
  p.ptr_location = LocMemory /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME sv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME dv /\
  value_has_type sv v /\ value_has_type dv v /\
  vv_holds ce cx (post_value_type ce e) raw (LocatedValue tag p) ee s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue tag p) ee G tn s ==>
  vv_holds ce cx (lowered_value_type ce e) raw
    (LocatedValue (lowered_value_type ce e) p) ee s /\
  ptr_vv_ok cx (lowered_value_type ce e) raw
    (LocatedValue (lowered_value_type ce e) p) ee G tn s
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  drule_all materialize_post_lowered_classify >> strip_tac
  >- gvs[vv_holds_def, ptr_vv_ok_def] >>
  irule extcall_request_bytestring_memory_retag >>
  metis_tac[]
QED
