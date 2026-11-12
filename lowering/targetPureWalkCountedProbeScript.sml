(* Counted execution interfaces for the zero-index candidate. *)
Theory targetPureWalkCountedProbe
Ancestors
  targetPureWalkSimulationProbe fragGasMode fragGasPath gasCount
  venomExecSemantics venomInst venomState compileEnv list

Theorem simulation_probe_invoke_count:
  !s id. gas_count_step 1 simulation_probe_context
    (mk_inst id INVOKE [Label simulation_probe_label] []) s = 0
Proof
  rpt gen_tac >>
  simp[Once gas_count_step_def, mk_inst_def, decode_invoke_def,
       simulation_probe_context_def, simulation_probe_callee_def,
       mk_venom_context_def, mk_raw_function_def, lookup_function_def,
       FIND_thm, eval_operands_def, setup_callee_def] >>
  simp[Once gas_count_blocks_def, lookup_block_def, FIND_thm,
       eval_phis_def, phi_prefix_length_def] >>
  simp[Once gas_count_block_def, get_instruction_def] >>
  simp[Once gas_count_step_def, is_terminator_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs,
       eval_operands_def, eval_operand_def] >>
  qmatch_goalsub_abbrev_tac `run_block_non_phis 0 cc bb st` >>
  qabbrev_tac `rr = run_block_non_phis 0 cc bb st` >>
  qpat_x_assum `Abbrev (rr = _)` (K all_tac) >>
  Cases_on `rr` >> simp[Once gas_count_blocks_def]
QED

Theorem simulation_probe_invoke_edge:
  !fn s bb id.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id INVOKE [Label simulation_probe_label] []) ==>
    gas_path_edge simulation_probe_context fn s 0
      (OK (s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >> simp[gas_path_edge_def] >>
  qexists_tac `1` >>
  simp[simulation_probe_invoke_restores, simulation_probe_invoke_count,
       mk_inst_def, is_terminator_def]
QED
