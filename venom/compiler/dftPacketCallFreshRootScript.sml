Theory dftPacketCallFreshRoot
Ancestors
  dftPacketCallFreshEntry dftPacketFreshSingletonNormalize
  dftPacketChangedCallerSuccess dftPacketFreshCutGeometry dftPacketCutExtension
  dftPacketFreshChildStop dftPacketRowAlignment dftPacketObservationSuccess
  dftGasFromListReplayBoundary dftRunRel venomInst venomExecSemantics
  venomExecProofs dftIndexedExec list rich_list arithmetic

Theorem fresh_cut_shape[local]:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  m = phi_prefix_length bb.bb_instructions /\
  ((q < LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
    z = DROP m ps ++ TAKE q xs /\ k = LENGTH ps-m+q) \/
   (m <= l /\ l < LENGTH ps /\ z = DROP m (TAKE l ps) /\ k = l-m)) ==>
  z = TAKE k (DROP m bb.bb_instructions) /\
  k < LENGTH (DROP m bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) z
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `phi_prefix_length ps <= LENGTH ps` by simp[phi_prefix_length_le] >>
  gvs[dft_phi_prefix_append, DROP_APPEND1, TAKE_APPEND2,
      TAKE_APPEND1, DROP_TAKE, EVERY_DROP, EVERY_TAKE]
QED
