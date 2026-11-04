Theory fragGasSeqAbort
Ancestors
  fragGasMode fragGasSeq fragGasSeqMem fragExec fragExecMem
  exprLoweringProps venomInst venomState list rich_list

(* A failing instruction ends the executed prefix. Reads in the unexecuted
   remainder do not contribute to its count. *)
Theorem run_inst_seq_abort_gas_path:
  !memory code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    (memory ==> run_inst_seq_mem_ok code s) /\
    run_inst_seq code s = Abort a t ==>
    ?n j. gas_marked_path memory ctx func s n
      (Abort a (t with vs_inst_idx := j))
Proof
  Cases_on `memory` >> simp[gas_marked_path_def]
QED
