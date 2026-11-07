Theory lowerDloadBytesEffects
Ancestors
  lowerDloadMacroBoundary lowerDloadPureEffects lowerDloadCleanCopy
  venomExecSemantics venomState finite_map list words pred_set ptrDiscipline

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

Theorem ld_bytes_completed_mem_taint:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  eval_operand dst t0 = SOME d /\ eval_operand sz t0 = SOME n /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  u.t_mem = u0.t_mem DIFF {b | w2n d <= b /\ b < w2n d + w2n n}
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  `step_inst 0 C a t0 = OK (update_var av (x+y) t0)` by
    (drule_all ld_macro_add_step >> simp[]) >>
  `(step_taint a t0 (update_var av (x+y) t0) u0).t_mem = u0.t_mem` by
    (irule (cj 1 ld_pure_taint_nonvar) >> simp[] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `step_taint c r z w` >>
  `eval_operand dst r = SOME d /\ eval_operand sz r = SOME n` by
    (simp[Abbr `r`] >> Cases_on `dst` >> Cases_on `sz` >>
     gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `step_inst 0 C c r = OK z` by
    (drule_all ld_macro_copy_step >> simp[] >>
     simp[Abbr `r`, Abbr `z`, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE]) >>
  drule_at (Pat `step_inst _ _ _ _ = _`) ld_clean_copy_mem_taint >>
  simp[Abbr `w`]
QED

Theorem ld_bytes_completed_memory:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  eval_operand dst t0 = SOME d /\ eval_operand off t0 = SOME x /\
  eval_operand sz t0 = SOME n /\ eval_operand (Label "code_end") t0 = SOME y /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  t.vs_memory = (write_memory_with_expansion (w2n d)
    (TAKE (w2n n) (DROP (w2n (x+y)) t0.vs_code ++ REPLICATE (w2n n) 0w)) t0).vs_memory
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[write_memory_with_expansion_def, expand_memory_def, write_memory_def,
       update_var_def]
QED

Theorem ld_bytes_completed_taint_effects:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  c.inst_outputs = [] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  u.t_var = u0.t_var |+ (av,{}) /\
  u.t_stor = u0.t_stor /\ u.t_trans = u0.t_trans /\ u.t_imm = u0.t_imm
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[step_taint_def, set_var_taint_def, out_taint_def,
       adopt_reset_def, store_taint_def, imm_taint_def] >>
  gvs[DRESTRICT_UNIV]
QED
