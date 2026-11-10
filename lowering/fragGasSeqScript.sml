(* Successful straight-line execution with the exact number of GAS reads. *)
Theory fragGasSeq
Ancestors
  fragGasPath fragExec gasCount exprLoweringProps instIdxIndep
  venomExecSemantics venomInstProofs venomInst venomState list rich_list arithmetic

Theorem tuple_straight_line_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK u ==>
  gas_path_edge ctx func s (if i.inst_opcode = GAS then 1 else 0)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[venomInstProofsTheory.step_preserves_halted] >>
  simp[gas_path_edge_def] >> qexists_tac `0` >> simp[gas_count_step_def]
QED

Theorem tuple_run_inst_seq_gas_path:
  !code s t ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK t ==>
    gas_path ctx func s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  Induct >> simp[run_inst_seq_def]
  >- (rpt strip_tac >> irule (cj 1 gas_path_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX code rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_DROP]) >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (simp[venomInstTheory.get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = rest` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
     simp[DROP_DROP, ADD1]) >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_halted,
              venomInstProofsTheory.step_preserves_control_flow] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `gas_path_edge ctx func s (if h.inst_opcode = GAS then 1 else 0)
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule tuple_straight_line_edge >> metis_tac[]) >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  disch_then (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `h.inst_opcode = GAS` >> gvs[] >>
  drule (cj 2 gas_path_rules) >> disch_then drule >>
  rewrite_tac[GSYM ADD1, ADD_CLAUSES, ONE]
QED
