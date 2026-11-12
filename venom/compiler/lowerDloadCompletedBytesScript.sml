Theory lowerDloadCompletedBytes
Ancestors
  lowerDloadMacroBoundary lowerDloadCopyReadback lowerDloadPairedBoundary
  lowerDloadOwnership lowerDloadPhaseBoundary ptrDiscipline venomExecSemantics venomState
  venomInstProofs venomExecProofs venomInst finite_map list words

Theorem ld_bytes_completed_readback:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C [a;c] t0 un (SUC (SUC 0)) t u /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand off t0 = SOME x /\ eval_operand dst t0 = SOME p /\
  eval_operand sz t0 = SOME n /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  w2n x + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256) ==>
  TAKE (w2n n) (DROP (w2n p) t.vs_memory) =
    TAKE (w2n n) (DROP (w2n x) s.vs_data_section ++ REPLICATE (w2n n) 0w)
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion _ _ r` >>
  `r.vs_code = s.vs_code` by simp[Abbr `r`, update_var_def] >>
  drule_all (SRULE [] ld_codecopy_readback) >> simp[]
QED

Theorem ld_bytes_completed_owned:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  c.inst_outputs = [] /\ av NOTIN V /\
  (!v. dst = Var v ==> v <> av) /\ (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C' [a;c] t0 un (SUC (SUC 0)) t u /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  inst.inst_outputs = [] /\ ld_owned_vars V E AG AH tn un s t0 /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN V) ==>
  ?z. step_inst fuel C inst s = OK z /\
    ld_owned_vars V E AG (ld_set_prov AH [av] NONE)
      (step_taint inst s z tn) u z t
Proof
  strip_tac >>
  drule_all ld_bytes_completed_source_success >>
  disch_then (qspecl_then [`fuel`,`C`] strip_assume_tac) >>
  qexists_tac `z` >> simp[] >>
  drule_all step_inst_preserves_labels_always >> strip_tac >>
  drule step_preserves_non_output_vars >>
  simp[is_terminator_def] >> strip_tac >>
  drule_all ld_bytes_completed_projections >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once ld_target_prefix_step_iff] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `0`] ld_target_prefix_step_iff)),
    ld_target_prefix_empty] >> strip_tac >>
  fs[ld_owned_vars_def] >>
  qx_gen_tac `name` >> strip_tac >> `name <> av` by metis_tac[] >>
  qpat_x_assum `!v. v IN V ==> _` (qspec_then `name` mp_tac) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    ld_set_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
    step_taint_def, set_var_taint_def]
QED
