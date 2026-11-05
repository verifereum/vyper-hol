Theory lowerDloadBytesEffects
Ancestors
  lowerDloadMacroBoundary venomExecSemantics venomState finite_map list

(* Allocation projections are already exported by ld_bytes_completed_projections. *)
Theorem ld_bytes_completed_params:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  t.vs_params = t0.vs_params
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[write_memory_with_expansion_def, expand_memory_def, write_memory_def,
    update_var_def]
QED

Theorem ld_bytes_completed_lookup:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  !v. v <> av ==> lookup_var v t = lookup_var v t0
Proof
  strip_tac >> drule_all ld_bytes_completed_projections >> strip_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
