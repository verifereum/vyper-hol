Theory makeSsaCurrentPrefixEffect
Ancestors
  makeSsaCurrentPrefixRuntime o1FrameLockstep livenessDefs
  venomExecSemantics venomWf venomInst list simplifyCfgRetpc
Theorem current_prefix_phi_eff_selected:
  !pre inst rest x p v.
  EVERY (\j. j.inst_opcode = PHI /\ ~MEM x j.inst_outputs) pre /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [x] /\
  phi_well_formed inst.inst_operands /\
  ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
  MEM (p,v) (phi_pairs inst.inst_operands) ==>
  phi_eff (SOME p) x (pre ++ inst::rest) = SOME (Var v)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[phi_eff_def, phi_read_def] >>
      metis_tac[retpc_phi_pair_selected]) >>
  gvs[] >>
  simp[phi_eff_def, phi_read_def] >>
  first_x_assum drule >> simp[phi_eff_def]
QED

Theorem current_prefix_phi_eff_absent:
  !insts prev x.
  EVERY (\j. ~MEM x j.inst_outputs) (collect_phis insts) ==>
  phi_eff prev x insts = SOME (Var x)
Proof
  Induct >- simp[phi_eff_def, phi_read_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[collect_phis_def, phi_eff_def, phi_read_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[phi_eff_def]
QED
