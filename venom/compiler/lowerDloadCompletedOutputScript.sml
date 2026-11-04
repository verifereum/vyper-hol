Theory lowerDloadCompletedOutput
Ancestors
  o1ContractLowerDloadTaint lowerDloadMacroBoundary lowerDloadPhaseBoundary
  ptrDiscipline venomExecSemantics venomState finite_map list words lowerDloadDefs
  lowerDloadCopyReadback lowerDloadPairedBoundary lowerDloadOwnership

Theorem ld_load_completed_output_clean:
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  FLOOKUP u.t_var out = SOME {}
Proof
  strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once ld_target_prefix_step_iff] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[SRULE [] (Q.INST [`n` |-> `2`] ld_target_prefix_step_iff)] >>
  strip_tac >>
  drule_all codecopy_mload_cleared >>
  disch_then (qspec_then `w'` assume_tac) >>
  `out_taint w d v = {}` by gvs[out_taint_def, ld_macro_operand_pc] >>
  simp[step_taint_def, set_var_taint_def, FLOOKUP_UPDATE]
QED

Theorem ld_load_completed_value[local]:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand off t0 = SOME x /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  w2n x + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256) /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  lookup_var out t = SOME (word_of_bytes T 0w
    (TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w)))
Proof
  strip_tac >>
  drule_all ld_load_fourth_prefix >> disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_third_prefix) >> disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_second_values) >> strip_tac >>
  gvs[] >>
  qpat_x_assum `eval_operand (Var av) (_ with vs_inst_idx := _) = _`
    (assume_tac o SRULE [ld_macro_operand_pc, eval_operand_def, lookup_var_def,
      write_memory_with_expansion_def]) >>
  gvs[eval_operand_def, lookup_var_def] >>
  qmatch_goalsub_abbrev_tac `mload (w2n p) copied` >>
  `TAKE 32 (DROP (w2n p) copied.vs_memory) =
    TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w)` by
    (qpat_x_assum `t0.vs_code = _` kall_tac >>
     drule_all (SRULE [] ld_codecopy_readback) >>
     disch_then assume_tac >> gvs[] >> simp[Abbr `copied`]) >>
  `LENGTH (TAKE 32 (DROP (w2n p) copied.vs_memory)) = 32` by simp[] >>
  `32 <= LENGTH (DROP (w2n p) copied.vs_memory)` by
    (qpat_x_assum `TAKE 32 _ = _` kall_tac >> gvs[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF, AllCaseEqs()]) >>
  simp[update_var_def, FLOOKUP_UPDATE, mload_def, TAKE_APPEND1]
QED

