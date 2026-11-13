(* Memory-length growth at concrete primitive encoder endpoints.
   The primitive contracts are strengthened in LeavesMem; sequence growth
   reuses the common opcode proof rather than reproving execution. *)
Theory abiEncoderWindowPrimitiveGrowthMem
Ancestors
  abiEncoderWindowLeavesMem abiEncoderWindowPrimitiveFrameMem
  stmtSimLogEncodeFrame stmtSimLogExecFields
  abiEncoderWindowSequence list pred_set

Theorem window_seq_memory_growth:
  window_seq st en s raw /\
  EVERY (\i. i.inst_opcode IN {ALLOCA; MLOAD; MSTORE; MCOPY; ADD; AND; NOT})
    (emitted_insts st en) ==>
  LENGTH s.vs_memory <= LENGTH raw.vs_memory
Proof
  strip_tac >> irule log_encode_run_memory_mono >>
  qexists `emitted_insts st en` >>
  fs[window_seq_def, EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]
QED
