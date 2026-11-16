Theory gasFocusBlockEventPrefix
Ancestors
  gasEvents dftIndexedExec rich_list list venomInst venomState

(* A finite executed prefix keeps completed INVOKE events: both collectors
   inspect the same instruction, state and fuel at every step. *)
Theorem focus_block_events_prefix:
  !k (s:venom_state) t.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons fuel C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t ==>
    ?later.
      gas_events_block fuel C owner bb s =
      gas_events_block fuel C owner
        (bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions) s ++ later
Proof
  Induct_on `k`
  >- (simp[] >> rpt strip_tac >>
      `gas_events_block fuel C owner
         (bb with bb_instructions := TAKE s.vs_inst_idx bb.bb_instructions) s = []` by
        simp[Once gas_events_block_def, get_instruction_def, LENGTH_TAKE] >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by
      simp[DROP_CONS_EL] >>
  gvs[TAKE_def, dft_exec_cons_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `t' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (EL s.vs_inst_idx bb.bb_instructions)` by simp[get_instruction_def] >>
  `get_instruction
      (bb with bb_instructions := TAKE (SUC k + s.vs_inst_idx) bb.bb_instructions)
      s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def, EL_TAKE] >>
  drule gas_events_block_at >>
  disch_then (qspecl_then [`fuel`,`C`,`owner`] assume_tac) >>
  qpat_x_assum `get_instruction (_ with bb_instructions := _) _ = _` kall_tac >>
  drule gas_events_block_at >>
  disch_then (qspecl_then [`fuel`,`C`,`owner`] assume_tac) >>
  gvs[arithmeticTheory.ADD_CLAUSES, APPEND_ASSOC] >>
  metis_tac[]
QED
