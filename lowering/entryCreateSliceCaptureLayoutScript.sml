(* The source-capture intervals of ordinary Slice have no administrative calls. *)
Theory entryCreateSliceCaptureLayout
Ancestors
  exprSimSliceCaptureControl exprSimSliceMemory abiBufferAllocationCode
  abiEncoderProps emitHelperProps exprLoweringProps venomInst arithmetic list

Theorem slice_dynamic_capture_admin_layout:
  compile_bytestring_src src sa = ((len,data),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule slice_bytestring_src_control >> strip_tac >>
  drule slice_bytestring_src_shape >>
  simp[mk_inst_def, frag_ids_def, is_terminator_def]
QED

Theorem slice_fixed_capture_admin_layout:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;src] sm = ((),sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_id IN frag_ids sa sb /\
             i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule emit_void_same_blocks >> strip_tac >>
  drule compile_alloc_buffer_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  fs[same_blocks_def, mk_inst_def, frag_ids_def, is_terminator_def, APPEND_ASSOC]
QED

Theorem slice_capture_admin_layout:
  (compile_bytestring_src src sa = ((len,data),sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_id IN frag_ids sa sb /\
               i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
               ~is_terminator i.inst_opcode) (emitted_insts sa sb)) /\
  (compile_alloc_buffer 32 sa = (buf,sm) /\
   emit_void MSTORE [buf.buf_operand;src] sm = ((),sb) ==>
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_id IN frag_ids sa sb /\
               i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
               ~is_terminator i.inst_opcode) (emitted_insts sa sb))
Proof
  conj_tac
  >- (strip_tac >> drule slice_dynamic_capture_admin_layout >> simp[]) >>
  strip_tac >> drule_all slice_fixed_capture_admin_layout >> simp[]
QED
