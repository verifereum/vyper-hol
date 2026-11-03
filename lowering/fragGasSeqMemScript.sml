(* A successful straight-line fragment counts every actual GAS site,
   including generated reads after the oracle is exhausted. *)
Theory fragGasSeqMem
Ancestors
  fragGasPathMem fragExecMem fragExec gasCount memSafeRun
  venomExecSemantics venomInstProofs venomState list rich_list arithmetic

Theorem straight_line_mem_edge[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i s /\ step_inst_base i s = OK u ==>
  gas_path_mem_edge ctx func s (if i.inst_opcode = GAS then 1 else 0)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  simp[gas_path_mem_edge_def] >>
  qexists_tac `0` >>
  simp[mem_safe_step_non_invoke, gas_count_step_def]
QED

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
