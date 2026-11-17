Theory dftPacketLiteralRowExtend
Ancestors
  dftPacketOperationalPrefix dftRunRel venomExecProofs
  venomExecSemantics venomInst venomState gasEvents list rich_list

Theorem dft_packet_literal_row_extend:
  !l bb z0 segment z1 f C owner
    (R : instruction list -> venom_state -> (string # num) list # exec_result) H.
  l = phi_prefix_length bb.bb_instructions /\
  z1 = z0 ++ segment /\
  z1 = TAKE (LENGTH z1) (DROP l bb.bb_instructions) /\
  LENGTH z1 <= LENGTH (DROP l bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z1 /\
  R = (\z ent. case eval_phis ent bb.bb_instructions of
    OK sp =>
      (gas_events_block f C owner
         (bb with bb_instructions := TAKE l bb.bb_instructions ++ z)
         (sp with vs_inst_idx := l),
       FOLDR (dft_exec_cons f C) OK z (sp with vs_inst_idx := l))
    | other => ([],other)) /\
  H = (\v.
      (gas_events_block f C owner
         (bb with bb_instructions := TAKE l bb.bb_instructions ++ z1) v,
       FOLDR (dft_exec_cons f C) OK segment v)) ==>
  !ent. R z1 ent =
    (case SND (R z0 ent) of
       OK v => (FST (R z0 ent) ++ FST (H v), SND (H v))
     | other => (FST (R z0 ent),other))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  `LENGTH (TAKE l bb.bb_instructions) = l` by
    (irule LENGTH_TAKE >> metis_tac[phi_prefix_length_le]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) z0` by gvs[EVERY_APPEND] >>
  qpat_x_assum `l = _` kall_tac >>
  qpat_x_assum `z1 = TAKE _ _` kall_tac >>
  qpat_x_assum `LENGTH z1 <= _` kall_tac >>
  qpat_x_assum `R = _` SUBST_ALL_TAC >>
  qpat_x_assum `H = _` SUBST_ALL_TAC >>
  Cases_on `eval_phis ent bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis ent bb.bb_instructions = OK sp` >>
  qspecl_then [`f`, `C`, `owner`,
    `bb with bb_instructions := TAKE l bb.bb_instructions ++ z1`,
    `sp with vs_inst_idx := l`, `LENGTH z0`] mp_tac
    dft_packet_block_prefix_operational >>
  simp[LET_THM, TAKE_APPEND, DROP_APPEND, DROP_TAKE, TAKE_LENGTH_TOO_LONG] >>
  strip_tac >>
  rewrite_tac[FOLDR_APPEND] >>
  Cases_on `FOLDR (dft_exec_cons f C) OK z0 (sp with vs_inst_idx := l)` >>
  gvs[] >>
  drule (Q.INST [`fuel` |-> `f`, `C` |-> `C`,
    `k` |-> `FOLDR (dft_exec_cons f C) OK segment`] dft_exec_prefix_continue) >>
  disch_then (qspecl_then [`segment`,`f`,`C`,`sp with vs_inst_idx := l`] mp_tac) >>
  simp[]
QED
