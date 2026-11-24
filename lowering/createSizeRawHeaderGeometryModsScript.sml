(* Allocation and byte widths at the actual raw CREATE snapshot site. *)
Theory createSizeRawHeaderGeometryMods
Ancestors
  createSizeRawHeaderGeometry createExprSizeExitDefsMods
  createBlueprintRawCopyLayoutMods exprLowering exprLoweringProps compileEnv
  copyExecution abiDecoderBytesTyped abiEncodeArgsCase loweringHalt
  exprPtrUnwrapAllocSeparation fragExec emitHelperProps loweringPosts
  exprSimHyps valueEncodingProps context words arithmetic pair

Theorem create_raw_header_capacity_mods:
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  lowered_value_type ce e = BaseT (BytesT (Dynamic n)) ==>
  32 <= type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size (BaseTV (BytesT (Dynamic n))) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) < 2 ** 64
Proof
  cheat
QED
