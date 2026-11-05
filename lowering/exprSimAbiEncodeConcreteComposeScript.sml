Theory exprSimAbiEncodeConcreteCompose
Ancestors
  exprSimAbiEncodeConcreteLeaves fragExec abiEncoderWindowSequence
  venomState venomExecSemantics venomInst list instIdxIndep exprLoweringProps

Theorem abi_encode_run_append_normalized:
  run_inst_seq xs s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\
  run_inst_seq ys (t with vs_inst_idx := k) = OK u ==>
  ?r. run_inst_seq (xs ++ ys) s = OK r /\
      (r with vs_inst_idx := n) = (u with vs_inst_idx := n)
Proof
  strip_tac >>
  drule run_inst_seq_inst_idx >>
  disch_then (qspecl_then [`t`, `k`] mp_tac) >>
  Cases_on `run_inst_seq ys t` >>
  gvs[exec_result_map_def] >> strip_tac >>
  qpat_assum `run_inst_seq xs s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then `ys` mp_tac) >> simp[] >> metis_tac[]
QED
