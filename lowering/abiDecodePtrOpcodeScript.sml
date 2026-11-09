Theory abiDecodePtrOpcode
Ancestors
  exprSimAbiDecodeFramed exprSimAbiDecodeResource
  exprSimAbiDecodeShape exprSimAbiDecodeShapeProbe exprSimAbiDecodeTrace exprSimAbiGasBridge
  fragExec compileEnv context venomInst pred_set sorting list

Theorem decode_framed_emitted_opcodes:
  decode_framed ex m post /\ m sa = (x,sb) /\
  sa.cs_blocks = sb.cs_blocks ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> PHI /\ i.inst_opcode <> STOP /\
    i.inst_opcode <> RETURN) (emitted_insts sa sb)
Proof
  strip_tac >>
  `?Q. decode_resource_run ex EMPTY m sa x sb Q` by
    (drule decode_framed_run >> disch_then drule >>
     disch_then (qspec_then `EMPTY` mp_tac) >> simp[] >> metis_tac[]) >>
  drule decode_resource_run_trace >> strip_tac >>
  `PERM (frag_code sa sb) (decode_instructions es)` by
    metis_tac[decode_replay_frag_code_history] >>
  fs[decode_trace_safe_def] >>
  `frag_code sa sb = emitted_insts sa sb` by
    simp[frag_code_def, emitted_blocks_def] >>
  metis_tac[PERM_EVERY]
QED
