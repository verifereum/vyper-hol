Theory lowerDloadCompletedOutput
Ancestors
  lowerDloadCleanCopy lowerDloadMacroBoundary lowerDloadPhaseBoundary
  ptrDiscipline venomExecSemantics venomState finite_map list words lowerDloadDefs pred_set
  lowerDloadCopyReadback lowerDloadPairedBoundary lowerDloadOwnership
  venomInstProofs venomExecProofs venomInst lowerDloadOperand

Theorem ld_load_completed_output_clean:
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  FLOOKUP u.t_var out = SOME {}
Proof
  strip_tac >>
  drule_all ld_load_fourth_prefix >> disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_third_prefix) >> disch_then (fn th => gvs[th]) >>
  `p = p'` by
    (gvs[ld_macro_operand_pc, eval_operand_def, lookup_var_def,
         write_memory_with_expansion_def]) >> gvs[] >>
  qmatch_goalsub_abbrev_tac `step_taint c r z w'` >>
  `step_inst 0 C c r = OK z` by
    (drule_all ld_macro_copy_step >> disch_then (fn th => rewrite_tac[th]) >>
     simp[Abbr `z`, eval_operand_def, dimword_def] >>
     gvs[eval_operand_def]) >>
  `eval_operand (Lit 32w) r = SOME 32w` by simp[eval_operand_def] >>
  `c.inst_opcode IN {DLOADBYTES; CODECOPY}` by simp[] >>
  drule_all ld_clean_copy_mem_taint >>
  disch_then (qspec_then `w'` assume_tac) >>
  `eval_operand (Var av) z = SOME p` by metis_tac[ld_macro_operand_pc] >>
  `out_taint (step_taint c r z w') d (z with vs_inst_idx := SUC r.vs_inst_idx) = {}` by
    (simp[out_taint_def, ld_macro_operand_pc, mem_word_taint_def,
          EXTENSION, dimword_def] >> decide_tac) >>
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


Theorem ld_step_taint_var_frame[local]:
  ~MEM v inst.inst_outputs ==>
  FLOOKUP (step_taint inst s z tn).t_var v = FLOOKUP tn.t_var v
Proof
  simp[step_taint_def, set_var_taint_def] >>
  Cases_on `inst.inst_outputs` >> simp[FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_load_completed_frame[local]:
  a.inst_opcode = ALLOCA /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_outputs = [bv] /\
  c.inst_opcode = CODECOPY /\ c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  t.vs_labels = t0.vs_labels /\
  !v. v <> av /\ v <> bv /\ v <> out ==>
    lookup_var v t = lookup_var v t0 /\
    op_taint u (Var v) = op_taint un (Var v)
Proof
  strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once ld_target_prefix_step_iff] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `2`] ld_target_prefix_step_iff))] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `1`] ld_target_prefix_step_iff))] >> strip_tac >>
  qpat_x_assum `ld_target_prefix _ _ _ _ _ _ _` mp_tac >>
  simp[Once (SRULE [] (Q.INST [`n` |-> `0`] ld_target_prefix_step_iff)), ld_target_prefix_empty] >>
  strip_tac >>
  imp_res_tac step_inst_preserves_labels_always >>
  imp_res_tac step_preserves_non_output_vars >>
  gvs[lookup_var_def, is_terminator_def] >>
  rpt strip_tac >> simp[op_taint_def, ld_step_taint_var_frame]
QED

Theorem ld_load_completed_owned:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\ av NOTIN V /\ bv NOTIN V /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t0 /\
  (!v. off = Var v ==> v IN V) /\ ld_op_prov AG off = NONE /\
  op_taint tn off = {} /\ eval_operand off s = SOME x /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  w2n x + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256) /\
  ld_target_prefix C' [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  ?z. step_inst fuel C inst s = OK z /\
    ld_owned_vars V E (ld_set_prov AG [out] NONE)
      (ld_set_prov (ld_set_prov AH [bv] NONE) [out] NONE)
      (step_taint inst s z tn) u z t
Proof
  strip_tac >>
  `eval_operand off t0 = SOME x` by metis_tac[ld_owned_operand_clean] >>
  `!v. off = Var v ==> v <> av` by metis_tac[] >>
  drule_all ld_load_completed_value >> strip_tac >>
  drule_all ld_load_completed_frame >> strip_tac >>
  drule_all ld_load_completed_output_clean >> strip_tac >>
  qexists_tac `update_var out
    (word_of_bytes T 0w (TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w))) s` >>
  conj_tac >- (asm_simp_tac (srw_ss()) [step_inst_non_invoke] >>
    pure_once_rewrite_tac[step_inst_base_def] >>
    qpat_assum `inst.inst_opcode = _` (fn th => pure_rewrite_tac[th]) >>
    simp[exec_read1_def]) >>
  fs[ld_owned_vars_def] >> conj_tac >- simp[update_var_def] >>
  qx_gen_tac `v` >> strip_tac >>
  Cases_on `v = out`
  >- (gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
        ld_set_prov_def, FLOOKUP_DRESTRICT, ld_owned_value_def,
        op_taint_def, step_taint_def, set_var_taint_def, out_taint_def,
        ld_mask_word_def]) >>
  `v <> av /\ v <> bv` by metis_tac[] >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    ld_set_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
    ld_step_taint_var_frame] >>
  strip_tac >> qpat_x_assum `!v. v IN V ==> _` (qspec_then `v` mp_tac) >>
  simp[lookup_var_def, op_taint_def]
QED
