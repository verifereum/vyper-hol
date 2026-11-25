(* Fetched occurrences of the successful straight and jump parts of a copy. *)
Theory slotCopyCursorWindow
Ancestors
  fragGasOrigin fragGasSeqAbort fragExec gasEvents
  venomInstProofs venomExecProofs venomExecSemantics venomState venomInst
  exprLoweringProps instIdxIndep relation rich_list list arithmetic

Definition slot_copy_walk_def:
  slot_copy_walk A explicit ctx func =
    RTC (\u v. ?bb i.
      lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME i /\
      A u.vs_current_bb u.vs_inst_idx i /\
      gas_origin_edge F explicit ctx func u [] (OK v))
End

Theorem slot_copy_walk_refl[simp]:
  slot_copy_walk A explicit ctx func s s
Proof
  simp[slot_copy_walk_def]
QED

Theorem slot_copy_walk_trans:
  transitive (slot_copy_walk A explicit ctx func)
Proof
  simp[slot_copy_walk_def, RTC_TRANSITIVE]
QED

Theorem slot_copy_walk_cons:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  A s.vs_current_bb s.vs_inst_idx i /\
  gas_origin_edge F explicit ctx func s [] (OK t) /\
  slot_copy_walk A explicit ctx func t r ==>
  slot_copy_walk A explicit ctx func s r
Proof
  rewrite_tac[slot_copy_walk_def] >> strip_tac >>
  irule (cj 2 RTC_RULES) >> qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem slot_copy_jump_window:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  A s.vs_current_bb s.vs_inst_idx i /\
  (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
  step_inst_base i s = OK (jump_to lbl s) ==>
  slot_copy_walk A explicit ctx func s (jump_to lbl s)
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ is_terminator i.inst_opcode` by
    gvs[is_terminator_def] >>
  `gas_origin_edge F explicit ctx func s [] (OK (jump_to lbl s))` by
    (simp[gas_origin_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_events_step_def] >> metis_tac[]) >>
  irule slot_copy_walk_cons >>
  (conj_tac >- (qexistsl_tac [`bb`, `i`] >> simp[]) >>
   qexists_tac `jump_to lbl s` >> simp[])
QED

Theorem slot_copy_straight_window:
  !code s raw bb A explicit ctx func.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> GAS) code /\
    run_inst_seq code s = OK raw /\
    (!j. j < LENGTH code ==> A s.vs_current_bb (s.vs_inst_idx+j) (EL j code)) ==>
    slot_copy_walk A explicit ctx func s
       (raw with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  Induct >- (rpt gen_tac >> strip_tac >> gvs[run_inst_seq_def] >>
             `s with vs_inst_idx := s.vs_inst_idx = s` by
               simp[venom_state_component_equality] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
     metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `gas_origin_edge F explicit ctx func s [] (OK t)` by
    (simp[gas_origin_edge_def] >> qexists_tac `0` >>
     simp[gas_events_step_def, Abbr `t`] >> metis_tac[]) >>
  `A s.vs_current_bb s.vs_inst_idx h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by gvs[EVERY_MEM] >>
  `run_inst_seq code t = OK (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `t`, run_inst_seq_inst_idx, exec_result_map_def] >>
  irule slot_copy_walk_cons >> simp[] >> qexists_tac `t` >> simp[] >>
  qpat_x_assum `!s raw bb A explicit ctx func. _`
    (qspecl_then [`t`, `raw with vs_inst_idx := SUC s.vs_inst_idx`,
                  `bb`, `A`, `explicit`, `ctx`, `func`] mp_tac) >>
  simp[Abbr `t`, ADD_CLAUSES, run_inst_seq_inst_idx, exec_result_map_def] >>
  disch_then irule >> rw[] >>
  first_x_assum (qspec_then `SUC j` mp_tac) >> simp[ADD_CLAUSES]
QED

Theorem slot_copy_walk_then:
  slot_copy_walk A explicit ctx func s t /\
  slot_copy_walk A explicit ctx func t r ==>
  slot_copy_walk A explicit ctx func s r
Proof
  metis_tac[slot_copy_walk_trans, transitive_def]
QED

Theorem slot_copy_window_then_jump:
  ~s.vs_halted /\ ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) code /\
  run_inst_seq code s = OK raw /\
  t = raw with vs_inst_idx := s.vs_inst_idx + LENGTH code /\
  get_instruction bb t.vs_inst_idx = SOME jump /\
  (jump.inst_opcode = JMP \/ jump.inst_opcode = JNZ) /\
  step_inst_base jump t = OK (jump_to lbl t) /\
  (!j. j < LENGTH (code ++ [jump]) ==>
       A s.vs_current_bb (s.vs_inst_idx+j) (EL j (code ++ [jump]))) ==>
  slot_copy_walk A explicit ctx func s (jump_to lbl t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `slot_copy_walk A explicit ctx func s t` by
    (qpat_assum `t = _ with vs_inst_idx := _` (pure_rewrite_tac o single) >>
     irule slot_copy_straight_window >> simp[] >>
     rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >>
     simp[EL_APPEND1]) >>
  `A t.vs_current_bb t.vs_inst_idx jump` by
    (first_x_assum (qspec_then `LENGTH code` mp_tac) >> simp[EL_APPEND2]) >>
  `slot_copy_walk A explicit ctx func t (jump_to lbl t)` by
    (irule slot_copy_jump_window >> gvs[] >> metis_tac[]) >>
  metis_tac[slot_copy_walk_then]
QED
