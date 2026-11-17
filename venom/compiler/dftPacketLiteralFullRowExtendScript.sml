Theory dftPacketLiteralFullRowExtend
Ancestors
  dftPacketOperationalPrefix dftRunRel venomExecProofs
  venomExecSemantics venomInst venomState gasEvents list rich_list

Theorem dft_packet_literal_full_row_extend:
  !l bb z0 xs Z f C owner
    (R : instruction list -> venom_state -> (string # num) list # exec_result) B.
  l = phi_prefix_length bb.bb_instructions /\
  Z = DROP l bb.bb_instructions /\ Z = z0 ++ xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) z0 /\
  R = (\z ent. case eval_phis ent bb.bb_instructions of
    OK sp =>
      (gas_events_block f C owner
         (bb with bb_instructions := TAKE l bb.bb_instructions ++ z)
         (sp with vs_inst_idx := l),
       FOLDR (dft_exec_cons f C) OK z (sp with vs_inst_idx := l))
    | other => ([],other)) /\
  B = (\u. (gas_events_block f C owner bb u,
    FOLDR (dft_exec_cons f C) OK xs u)) ==>
  !ent. R Z ent =
    (case SND (R z0 ent) of
       OK u => (FST (R z0 ent) ++ FST (B u), SND (B u))
     | r => (FST (R z0 ent),r))
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  `l <= LENGTH bb.bb_instructions` by metis_tac[phi_prefix_length_le] >>
  `l + LENGTH z0 <= LENGTH bb.bb_instructions` by
    (`LENGTH (DROP l bb.bb_instructions) = LENGTH z0 + LENGTH xs` by
       metis_tac[LENGTH_APPEND] >> gvs[LENGTH_DROP]) >>
  qpat_x_assum `l = _` kall_tac >>
  `bb with bb_instructions := TAKE l bb.bb_instructions ++ Z = bb` by
    (qpat_x_assum `Z = DROP _ _` (fn th => rewrite_tac[th, TAKE_DROP]) >> simp[]) >>
  `DROP l bb.bb_instructions = z0 ++ xs` by metis_tac[] >>
  qpat_x_assum `Z = DROP _ _` kall_tac >>
  `TAKE (l + LENGTH z0) bb.bb_instructions =
    TAKE l bb.bb_instructions ++ z0` by simp[TAKE_SUM, TAKE_APPEND] >>
  qpat_x_assum `R = _` SUBST_ALL_TAC >>
  qpat_x_assum `B = _` SUBST_ALL_TAC >>
  Cases_on `eval_phis ent bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis ent bb.bb_instructions = OK sp` >>
  qspecl_then [`f`, `C`, `owner`, `bb`,
    `sp with vs_inst_idx := l`, `LENGTH z0`] mp_tac
    dft_packet_block_prefix_operational >>
  simp[LET_THM, TAKE_APPEND] >> strip_tac >>
  rewrite_tac[FOLDR_APPEND] >>
  Cases_on `FOLDR (dft_exec_cons f C) OK z0 (sp with vs_inst_idx := l)` >>
  gvs[] >>
  drule (Q.INST [`fuel` |-> `f`, `C` |-> `C`,
    `k` |-> `FOLDR (dft_exec_cons f C) OK xs`] dft_exec_prefix_continue) >>
  disch_then (qspecl_then [`xs`,`f`,`C`,`sp with vs_inst_idx := l`] mp_tac) >>
  simp[]
QED
