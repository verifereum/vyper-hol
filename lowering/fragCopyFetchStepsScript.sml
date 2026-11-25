(* Introduce guarded edges from the concrete list and branch executions. *)
Theory fragCopyFetchSteps
Ancestors
  fragCopyFetchRun fragGasSeqAbort fragGasOrigin fragExec gasEvents
  exprLoweringProps instIdxIndep venomExecSemantics venomInstProofs1 venomState venomInst
  list rich_list arithmetic

Theorem copy_fetch_run_seq:
  !code s raw.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) code /\
    (!j. j < LENGTH code ==>
      Q s.vs_current_bb (s.vs_inst_idx+j) (EL j code).inst_id) /\
    run_inst_seq code s = OK raw ==>
    copy_fetch_run Q E C f s
      (raw with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  Induct
  >- (simp[run_inst_seq_def] >> rpt strip_tac >>
      `s with vs_inst_idx := s.vs_inst_idx = s` by
        simp[venom_state_component_equality] >> simp[]) >>
  rpt gen_tac >> simp[Once run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base h s = OK u` >>
  `isPREFIX (h::code) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[Once rich_listTheory.IS_PREFIX] >>
  drule instruction_prefix_cursor >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (drule_all step_inst_base_preserves_all >> simp[]) >>
  qabbrev_tac `m = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_origin_edge F E C f s [] (OK m)` by
    (simp[gas_origin_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def, Abbr `m`]) >>
  `Q s.vs_current_bb s.vs_inst_idx h.inst_id` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `copy_fetch_run Q E C f s m` by (irule copy_fetch_run_edge >> metis_tac[]) >>
  `run_inst_seq code m = OK (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
     simp[Abbr `m`, run_inst_seq_inst_idx, exec_result_map_def]) >>
  `!j. j < LENGTH code ==> Q m.vs_current_bb (m.vs_inst_idx+j) (EL j code).inst_id` by
    (rpt strip_tac >>
     qpat_x_assum `!k. k < SUC (LENGTH code) ==> _` (qspec_then `SUC j` mp_tac) >>
     simp[Abbr `m`, ADD_CLAUSES, EL]) >>
  irule copy_fetch_run_trans >> qexists_tac `m` >> simp[] >>
  first_x_assum (qspecl_then [`m`,`raw with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[Abbr `m`, ADD_CLAUSES]
QED

Theorem copy_fetch_run_jump:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  Q s.vs_current_bb s.vs_inst_idx i.inst_id /\
  (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
  step_inst_base i s = OK (jump_to lbl s) ==>
  copy_fetch_run Q E C f s (jump_to lbl s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ is_terminator i.inst_opcode` by
    (qpat_assum `i.inst_opcode = JMP \/ _` strip_assume_tac >> simp[is_terminator_def]) >>
  `gas_origin_edge F E C f s [] (OK (jump_to lbl s))` by
    (simp[gas_origin_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `lbl` >> simp[]) >>
  irule copy_fetch_run_edge >> metis_tac[]
QED
