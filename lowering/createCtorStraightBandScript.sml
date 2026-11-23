(* Record the computed endpoint of a straight sequence in an enclosing ID band. *)
Theory createCtorStraightBand
Ancestors
  createCtorSegmentArrival fragExec exprLoweringProps venomExecSemantics
  venomInstProofs venomInst venomState instIdxIndep list rich_list relation arithmetic

Theorem ctor_straight_band_run:
  !code s t bb fn lo hi.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. lo <= i.inst_id /\ i.inst_id < hi) code /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK t ==>
    RTC (\u v. ?i. ctor_segment_fetch fn u = SOME i /\
                    lo <= i.inst_id /\ i.inst_id < hi /\
                    i.inst_opcode <> INVOKE /\
                    ctor_segment_next fn u i = SOME v)
        s (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  rpt gen_tac >> map_every qid_spec_tac [`t`, `s`, `code`] >>
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK mid` >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX code rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  drule DROP_EQ_CONS >> strip_tac >>
  `mid.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  irule (CONJUNCT2 (SPEC_ALL RTC_RULES)) >>
  qexists_tac `mid with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac
  >- (BETA_TAC >> qexists_tac `h` >>
      simp[ctor_segment_fetch_def, get_instruction_def, ctor_segment_next_def]) >>
  first_x_assum (qspecl_then [`mid with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  fs[run_inst_seq_inst_idx, exec_result_map_def, ADD1]
QED
