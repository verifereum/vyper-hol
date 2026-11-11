(* Counted terminal RET, with arbitrary payload and return-PC operands. *)
Theory bodyIntCallFamStmtReturnStackPath
Ancestors
  bodyIntCallReachableReturn stmtSimReturn fnFrameBoundaryGenRet
  fragGasPath fragGasMode fragGasSeq gasCount instIdxIndep venomExecSemantics
  venomState venomInst list rich_list

Theorem step_ret_operands:
  eval_operands ops s = SOME vals /\ eval_operand rpc s = SOME pc ==>
  step_inst_base (mk_inst iid RET (ops ++ [rpc]) []) s =
    IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> s
Proof
  strip_tac >>
  `eval_operands (ops ++ [rpc]) s = SOME (vals ++ [pc])` by
    simp[eval_operands_append, eval_operands_def] >>
  Cases_on `vals` >>
  simp[step_inst_base_def, mk_inst_def, FRONT_CONS_NOT_NIL,
       FRONT_APPEND]
QED

Theorem run_inst_seq_values_ret_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq code s = OK u /\
  u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
  get_instruction bb (s.vs_inst_idx + LENGTH code) =
    SOME (mk_inst iid RET (ops ++ [rpc]) []) /\
  eval_operands ops u = SOME vals /\ eval_operand rpc u = SOME pc ==>
  gas_path ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|>
       (u with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  strip_tac >>
  drule_all tuple_run_inst_seq_gas_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_goalsub_abbrev_tac `IntRet ir land` >>
  `gas_path ctx func land 0 (IntRet ir land)` by
    (irule (cj 3 gas_path_rules) >> simp[fragExecTheory.exit_result_def] >>
     simp[gas_path_edge_def, Abbr `land`] >>
     qexistsl_tac [`0`, `mk_inst iid RET (ops ++ [rpc]) []`] >>
     simp[gas_count_step_def] >>
     conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >> disj2_tac >>
     `step_inst_base (mk_inst iid RET (ops ++ [rpc]) [])
        (u with vs_inst_idx := LENGTH code + s.vs_inst_idx) =
        IntRet ir (u with vs_inst_idx := LENGTH code + s.vs_inst_idx)` by
       (simp[Abbr `ir`] >> irule step_ret_operands >>
        simp[eval_op_inst_idx, eval_ops_inst_idx]) >>
     simp[step_inst_non_invoke, fragExecTheory.exit_result_def]) >>
  drule gas_path_then >> disch_then drule >> simp[Abbr `land`]
QED
