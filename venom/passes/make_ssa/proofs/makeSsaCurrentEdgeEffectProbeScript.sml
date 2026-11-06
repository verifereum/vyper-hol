Theory makeSsaCurrentEdgeEffectProbe
Ancestors
  makeSsaCurrentPrefixEffect o1FrameLockstep venomExecSemantics venomWf venomInst list

(* Selected operands reduce the syntactic interface to one incoming lookup;
   no value equality or assumed block agreement is used. *)
Theorem current_edge_retained_effect_reduction:
  EVERY (\j. j.inst_opcode = PHI /\ ~MEM x j.inst_outputs) pre /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [x] /\
  phi_well_formed inst.inst_operands /\
  ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
  MEM (p,v) (phi_pairs inst.inst_operands) /\
  EVERY (\j. j.inst_opcode = PHI /\ ~MEM y j.inst_outputs) pre' /\
  inst'.inst_opcode = PHI /\ inst'.inst_outputs = [y] /\
  phi_well_formed inst'.inst_operands /\
  ALL_DISTINCT (MAP FST (phi_pairs inst'.inst_operands)) /\
  MEM (p,n) (phi_pairs inst'.inst_operands) ==>
  (OPTREL (op_rename incoming)
    (phi_eff (SOME p) x (pre ++ inst::rest))
    (phi_eff (SOME p) y (pre' ++ inst'::rest')) <=>
   FLOOKUP incoming n = SOME v)
Proof
  strip_tac >>
  `phi_eff (SOME p) x (pre ++ inst::rest) = SOME (Var v)` by
    metis_tac[current_prefix_phi_eff_selected] >>
  `phi_eff (SOME p) y (pre' ++ inst'::rest') = SOME (Var n)` by
    metis_tac[current_prefix_phi_eff_selected] >>
  simp[op_rename_def]
QED
