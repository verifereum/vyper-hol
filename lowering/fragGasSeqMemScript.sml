(* A successful straight-line fragment counts every actual GAS site,
   including generated reads after the oracle is exhausted. *)
Theory fragGasSeqMem
Ancestors
  fragGasPathMem fragExecMem fragExec gasCount memSafeRun
  venomExecSemantics venomInstProofs venomState list rich_list arithmetic

Theorem run_inst_seq_gas_path_mem:
  !code s t ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    run_inst_seq code s = OK t ==>
    gas_path_mem ctx func s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  cheat
QED
