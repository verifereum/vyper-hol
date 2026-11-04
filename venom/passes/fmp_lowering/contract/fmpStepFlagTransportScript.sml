Theory fmpStepFlagTransport
Ancestors
  dftCallChecks unitShapeDefs venomEffects list

Definition flag_step_def:
  flag_step inst vs =
    if write_effects inst.inst_opcode <> empty_effects then []
    else case (inst.inst_opcode, inst.inst_operands) of
      (ASSIGN, [Var u]) =>
        if MEM u vs then inst.inst_outputs ++ vs
        else FILTER (\x. ~MEM x inst.inst_outputs) vs
    | _ => FILTER (\x. ~MEM x inst.inst_outputs) vs
End

Theorem flag_path_cons_step:
  flag_path bbs vs (i::rest) <=>
  i.inst_opcode <> INVOKE /\
  (flag_fails bbs vs i \/ flag_path bbs (flag_step i vs) rest)
Proof
  simp[flag_path_def, flag_step_def]
QED

Theorem flag_step_closed:
  EVERY (\x. MEM x V) vs /\
  EVERY (\x. MEM x V) i.inst_outputs ==>
  EVERY (\x. MEM x V) (flag_step i vs)
Proof
  rpt strip_tac >> gvs[EVERY_MEM] >>
  simp[flag_step_def] >>
  Cases_on `write_effects i.inst_opcode = empty_effects` >> simp[] >>
  Cases_on `i.inst_opcode` >>
  simp[EVERY_MEM, MEM_FILTER] >>
  TRY (rpt strip_tac >> first_x_assum irule >> simp[] >> NO_TAC) >>
  Cases_on `i.inst_operands` >> simp[EVERY_MEM, MEM_FILTER] >>
  TRY (rpt strip_tac >> first_x_assum irule >> simp[] >> NO_TAC) >>
  Cases_on `h` >> simp[EVERY_MEM, MEM_FILTER] >>
  TRY (rpt strip_tac >> first_x_assum irule >> simp[] >> NO_TAC) >>
  Cases_on `t` >> simp[EVERY_MEM, MEM_FILTER] >>
  Cases_on `MEM s vs` >> gvs[EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem flag_step_preserves_disjoint:
  write_effects i.inst_opcode = empty_effects /\
  EVERY (\x. ~MEM x vs) i.inst_outputs ==>
  !x. MEM x vs ==> MEM x (flag_step i vs)
Proof
  rpt strip_tac >>
  `~MEM x i.inst_outputs` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[flag_step_def] >>
  Cases_on `i.inst_opcode` >> simp[MEM_FILTER] >>
  Cases_on `i.inst_operands` >> simp[MEM_FILTER] >>
  Cases_on `h` >> simp[MEM_FILTER] >>
  Cases_on `t` >> simp[MEM_FILTER] >>
  Cases_on `MEM s vs` >> gvs[MEM_FILTER, EVERY_MEM] >> metis_tac[]
QED

Theorem flag_path_pure_prefix:
  !p bbs vs tail.
  EVERY (\i. i.inst_opcode <> INVOKE /\
    write_effects i.inst_opcode = empty_effects /\
    EVERY (\x. ~MEM x vs) i.inst_outputs) p /\
  flag_path bbs vs tail ==>
  flag_path bbs vs (p ++ tail)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  gvs[EVERY_DEF] >> simp[flag_path_cons_step] >>
  disj2_tac >> irule flag_path_mono >>
  qexists_tac `vs` >> conj_tac
  >- (rpt strip_tac >> irule flag_step_preserves_disjoint >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem flag_path_empty_pure_prefix:
  EVERY (\i. i.inst_opcode <> INVOKE /\
    write_effects i.inst_opcode = empty_effects) p /\
  flag_path bbs [] tail ==>
  flag_path bbs [] (p ++ tail)
Proof
  strip_tac >> irule flag_path_pure_prefix >>
  gvs[EVERY_MEM]
QED
