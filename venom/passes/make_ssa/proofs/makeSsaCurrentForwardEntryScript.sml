Theory makeSsaCurrentForwardEntry
Ancestors
  makeSsaCurrentPrefixRuntime o1FrameLockstep venomExecSemantics venomState

(* All PHI reads are from the pre-PHI state, including dead outputs. *)
Theorem current_forward_selected_phi_evaluable:
  phi_well_formed inst.inst_operands /\
  ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
  MEM (p,src) (phi_pairs inst.inst_operands) /\
  inst.inst_outputs = [dst] /\ st'.vs_prev_bb = SOME p /\
  state_rel sg st st' /\ FLOOKUP sg src = SOME v /\
  IS_SOME (lookup_var v st) ==>
  IS_SOME (eval_one_phi st' inst)
Proof
  strip_tac >>
  `resolve_phi p inst.inst_operands = SOME (Var src)` by
    metis_tac[current_prefix_resolve_phi_selected] >>
  `lookup_var src st' = lookup_var v st` by
    (fs[state_rel_def, vars_rel_def] >> metis_tac[]) >>
  Cases_on `lookup_var v st` >>
  gvs[eval_one_phi_def, eval_operand_def]
QED
