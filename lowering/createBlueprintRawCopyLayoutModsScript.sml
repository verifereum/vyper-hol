(* Capacity at the compiler's unmodified VV tag, and the live copy size. *)
Theory createBlueprintRawCopyLayoutMods
Ancestors
  createBlueprintRawCopyLayout createExprSizeExitDefsMods
  exprBodyPreProps exprReasonOperand exprSimIfExp exprSimHyps
  immutableDeployPhysicalSource abiEncodeArgsCase valueCopyBytes
  valueEncodingTyping vyperValue vyperTypeSystem
  exprSimHypsDefs exprSimProps context compileEnv

Theorem create_blueprint_raw_copy_layout_mods:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  bind (eval_expr cx e) (read_result cx) es = (INL (BytesV bytes),ee) ==>
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  value_has_type (BaseTV (BytesT (Dynamic k))) (BytesV bytes) /\
  ?p q.
    lowered_value_type ce e = BaseT (BytesT (Dynamic p)) /\
    vv_type vv = BaseT (BytesT (Dynamic q)) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) =
      SOME (BaseTV (BytesT (Dynamic p))) /\
    evaluate_type (get_tenv cx) (vv_type vv) =
      SOME (BaseTV (BytesT (Dynamic q))) /\
    value_has_type (BaseTV (BytesT (Dynamic p))) (BytesV bytes) /\
    value_has_type (BaseTV (BytesT (Dynamic q))) (BytesV bytes) /\
    val_wf (BaseTV (BytesT (Dynamic p))) (BytesV bytes) /\
    val_wf (BaseTV (BytesT (Dynamic q))) (BytesV bytes) /\
    type_memory_bytes ce (vv_type vv) = type_memory_size (BaseTV (BytesT (Dynamic q))) /\
    type_memory_size (BaseTV (BytesT (Dynamic q))) < 2 ** 64 /\
    type_memory_size (BaseTV (BytesT (Dynamic q))) + 64 < dimword (:256) /\
    val_store_size (BaseTV (BytesT (Dynamic p))) (BytesV bytes) =
      val_store_size (BaseTV (BytesT (Dynamic q))) (BytesV bytes) /\
    val_store_size (BaseTV (BytesT (Dynamic p))) (BytesV bytes) <=
      type_memory_size (BaseTV (BytesT (Dynamic p))) /\
    val_store_size (BaseTV (BytesT (Dynamic q))) (BytesV bytes) <=
      type_memory_size (BaseTV (BytesT (Dynamic q)))
Proof
  cheat
QED
