Theory abiDecodeScalarRunSafety
Ancestors
  bodyPtrBopScalarOutcome bodyFullAbiDecodeClampMemory venomInst list

Theorem abi_decode_scalar_run_safe:
  bop_scalar_seq R A code B ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s
Proof
  strip_tac >> conj_tac
  >- (simp[EVERY_MEM] >> rpt gen_tac >> disch_tac >>
      drule_all bop_scalar_seq_outputs >>
      disch_then (mp_tac o CONJUNCT1) >> simp[MEM] >>
      strip_tac >> simp[is_terminator_def]) >>
  metis_tac[abi_decode_scalar_seq_mem_ok]
QED
