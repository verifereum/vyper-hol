Theory dftPacketOperationalPrefix
Ancestors
  dftNativePlanPrefix dftIndexedExec gasEvents
  venomExecSemantics venomInst venomState opcodeClass list rich_list arithmetic

Theorem dft_packet_plain_prefix_no_intret:
  !xs f C s.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) xs ==>
    !ir t. FOLDR (dft_exec_cons f C) OK xs s <> IntRet ir t
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  simp[dft_exec_cons_def] >>
  `!ir t. step_inst f C h s <> IntRet ir t` by
    (simp[step_inst_non_invoke] >> metis_tac[step_inst_base_no_intret]) >>
  Cases_on `step_inst f C h s` >> simp[]
QED

Theorem dft_packet_plain_prefix_index[local]:
  !xs f C s t.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    FOLDR (dft_exec_cons f C) OK xs s = OK t ==>
    t.vs_inst_idx = s.vs_inst_idx + LENGTH xs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[dft_exec_cons_def, AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem dft_packet_block_prefix_operational:
  !f C owner bb s k.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) ==>
    let xs = TAKE k (DROP s.vs_inst_idx bb.bb_instructions);
        cut = bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions;
        r = FOLDR (dft_exec_cons f C) OK xs s
    in
      (!t. r = OK t ==>
        t.vs_inst_idx = s.vs_inst_idx + k /\
        exec_block f C bb s = exec_block f C bb t /\
        gas_events_block f C owner bb s =
          gas_events_block f C owner cut s ++ gas_events_block f C owner bb t) /\
      (~(?t. r = OK t) ==>
        exec_block f C bb s = r /\
        gas_events_block f C owner bb s = gas_events_block f C owner cut s)
Proof
  rpt gen_tac >> strip_tac >> simp_tac (srw_ss()) [LET_THM] >>
  qspecl_then
    [`TAKE k (DROP s.vs_inst_idx bb.bb_instructions)`, `s`, `bb`,
     `bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions`,
     `DROP k (DROP s.vs_inst_idx bb.bb_instructions)`]
    mp_tac (Q.INST [`sf` |-> `ARB with fn_name := owner`]
      native_list_prefix_boundary) >>
  simp[TAKE_DROP, DROP_TAKE] >>
  Cases_on `FOLDR (dft_exec_cons f C) OK
    (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s` >> simp[] >>
  rpt strip_tac >> simp[] >>
  drule_all dft_packet_plain_prefix_index >>
  simp[LENGTH_TAKE, LENGTH_DROP]
QED
