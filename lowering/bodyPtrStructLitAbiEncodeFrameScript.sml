Theory bodyPtrStructLitAbiEncodeFrame
Ancestors bodyPtrStructLitAbiEncodeShape bodyPtrStructLitOwnershipAbiEncode
  bodyPtrStructLitOwnershipStructFrame loweringShapeDefs loweringShapeRules
  abiEncoder context compileEnv

Theorem alloc_run_abi_encode_to_buf_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_to_buf dst src info)
    (\len s. shape_state s /\ R s /\ plain_operand s len)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[abi_encode_to_buf_shape, alloc_run_compile_abi_encode_to_buf]
QED
