Theory bodyPtrIfExpRuntimeSource
Ancestors bodyPtrIfExpBytesInputs bodyPtrIfExpMaterializeCapacity
  loweringPosts bodyPtrDefs vyperState valueEncodingProps arithmetic

(* Immutable descriptors depend on the captured result only through its
   read value.  Normalize that result without changing its annotation. *)
Theorem ifexp_immutable_holds_value:
  immutable_holds ce cx ann raw a ee s /\
  read_result cx raw ee = (INL v,ee) ==>
  immutable_holds ce cx ann (Value v) a ee s
Proof
  simp[immutable_holds_def, read_result_def, return_def] >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >> simp[]
QED

Theorem ifexp_runtime_arm_source:
  post_value_type ce e = expr_type e /\
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  pp.ptr_location = LocCode /\ ~ce.ce_is_ctor ==>
  ?a ty.
    tag = expr_type e /\
    eval_operand pp.ptr_operand s = SOME a /\
    op_taint tn pp.ptr_operand = {} /\
    immutable_holds ce cx (expr_type e) (Value v) a ee s /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    value_has_type ty v /\
    type_memory_bytes ce (expr_type e) = type_memory_size ty /\
    type_slot_size ty = (type_memory_bytes ce (expr_type e)+31) DIV 32 /\
    32*((type_memory_bytes ce (expr_type e)+31) DIV 32) =
      type_memory_bytes ce (expr_type e)
Proof
  strip_tac >> drule_all ifexp_arm_annotation_typed >> strip_tac >>
  drule_all ifexp_materialize_annotation_aligned >> strip_tac >>
  `tag = expr_type e /\ ?a. eval_operand pp.ptr_operand s = SOME a /\
    immutable_holds ce cx (expr_type e) raw a ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  drule_all ifexp_immutable_holds_value >> strip_tac >>
  fs[ptr_vv_ok_def] >>
  simp[type_memory_size_slots, MULT_DIV] >> metis_tac[]
QED
