Theory dftPacketCompletePlanOperational
Ancestors
  dftPacketRootedOperational dftPacketRowAlignment
  gasEvents venomExecSemantics dftIndexedExec list rich_list

Theorem dft_packet_complete_plan_operational:
  !F C sf a R P oldplan entry rows bb d z0 Z E v.
    R = (\(bb,e,z) s.
      case eval_phis s bb.bb_instructions of
        OK sp =>
          (gas_events_block (F-e) C sf.fn_name
            (bb with bb_instructions :=
              TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
           FOLDR (dft_exec_cons (F-e) C) OK z
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      | other => ([],other)) /\
    P = (\rows s. FOLDL (\(es,r) row. case r of
      OK t => (es ++ FST (R row t),SND (R row t))
    | other => (es,other)) ([],OK s) rows) /\
    (!i b e z. SUC i < LENGTH oldplan /\ EL i oldplan = (b,e,z) ==>
      e = a + SUC i /\ e <= F /\ b.bb_instructions <> [] /\
      is_terminator (LAST b.bb_instructions).inst_opcode /\
      z = DROP (phi_prefix_length b.bb_instructions) b.bb_instructions) /\
    (!i b e z es s. i < LENGTH oldplan /\ EL i oldplan = (b,e,z) /\
      P (TAKE i oldplan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME b /\
      (0 < i ==> ~s.vs_halted)) /\
    oldplan = rows ++ [(bb,d,z0)] /\ d = a + SUC (LENGTH rows) /\ d <= F /\
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    Z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
    P (rows ++ [(bb,d,Z)]) entry = (E,OK v) /\ ~v.vs_halted ==>
    run_blocks (F-a) C sf entry = run_blocks (F-d) C sf v /\
    gas_events_blocks (F-a) C sf entry = E ++ gas_events_blocks (F-d) C sf v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `P (rows ++ _) entry = _` mp_tac >>
  qpat_assum `P = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  disch_then (mp_then Any mp_tac dft_packet_plan_last_success) >> strip_tac >>
  `TAKE (LENGTH rows) oldplan = rows` by simp[TAKE_APPEND] >>
  `P (TAKE (LENGTH rows) oldplan) entry = (prior,OK s)` by (simp[] >> gvs[]) >>
  `run_blocks (F'-a) C sf entry = run_blocks (F'-(a+LENGTH rows)) C sf s /\
   gas_events_blocks (F'-a) C sf entry =
     prior ++ gas_events_blocks (F'-(a+LENGTH rows)) C sf s` by
    (`LENGTH rows < LENGTH oldplan` by simp[] >>
     irule dft_packet_plan_prefix_operational >>
     qexistsl_tac [`P`,`R`,`oldplan`] >> simp[NoAsms] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb sf.fn_blocks = SOME bb` by
    (qpat_x_assum `!i b e z es s. _` (qspec_then `LENGTH rows` mp_tac) >>
     simp[EL_APPEND2] >> metis_tac[]) >>
  qpat_x_assum `R _ _ = _` mp_tac >> simp[] >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >> strip_tac >>
  `F'-(a+LENGTH rows) = SUC (F'-d)` by decide_tac >>
  drule_all dft_packet_complete_row_operational >>
  simp[APPEND_ASSOC]
QED
