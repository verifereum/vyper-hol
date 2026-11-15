(* Leading copies before discarded ASSIGN/REVERT suffixes. *)
Theory readonlyInvokeCopyFwdHistoryCopyAbort
Ancestors
  readonlyInvokeCopyFwdHistoryAbort readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdRel taintAgree venomInst venomExecProps
  o1LowerDloadAvailableSuffix venomExecSemantics venomState
  finite_map list pred_set


Theorem ricf_history_copy_edit_fetch:
  ricf_block_edit bb bb' /\ get_instruction bb i = SOME ii /\
  ii.inst_opcode = MCOPY ==>
  ?jj. get_instruction bb' i = SOME jj /\
       (jj = ii \/ jj.inst_opcode = NOP)
Proof
  strip_tac >> drule ricf_block_edit_EL >>
  simp[get_instruction_def] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >>
  gvs[get_instruction_def, ricf_inst_edit_def] >> metis_tac[]
QED

Theorem ricf_history_copy_prefix_abort:
  ricf_block_edit bb bb' /\ ricf_frame_agree D X sites PG G tn s t /\
  s.vs_inst_idx = t.vs_inst_idx /\
  get_instruction bb s.vs_inst_idx = SOME ii /\
  ii.inst_opcode = MCOPY /\ ii.inst_operands = [dst; src; len] /\
  ii.inst_outputs = [] /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand len s = SOME nw /\
  get_instruction bb (SUC s.vs_inst_idx + d) = SOME ri /\
  ri.inst_opcode = REVERT /\
  (!k jj. k < d /\ get_instruction bb (SUC s.vs_inst_idx + k) = SOME jj ==>
          jj.inst_opcode = ASSIGN) /\
  exec_block fuel C bb s = Abort reason u ==>
  ?v. exec_block fuel C' bb' t = Abort reason v
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels /\ FDOM s.vs_vars = FDOM t.vs_vars` by
    gvs[ricf_frame_agree_def, taint_agree_def, venom_state_component_equality] >>
  `!op. IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t)` by
    (gen_tac >> irule ld_available_operand >>
     (reverse conj_tac >- simp[]) >> qexists_tac `UNIV` >>
     simp[FLOOKUP_DEF] >> gen_tac >> IF_CASES_TAC >> simp[]) >>
  `IS_SOME (eval_operand dst t) /\ IS_SOME (eval_operand src t) /\
   IS_SOME (eval_operand len t)` by metis_tac[optionTheory.IS_SOME_DEF] >>
  Cases_on `eval_operand dst t` >> gvs[] >>
  Cases_on `eval_operand src t` >> gvs[] >>
  Cases_on `eval_operand len t` >> gvs[] >>
  drule_all ricf_history_copy_edit_fetch >> strip_tac >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[is_terminator_def] >> strip_tac >>
  gvs[] >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[is_terminator_def] >>
  drule_at (Pat `exec_block _ _ _ _ = _`)
    ld_available_suffix_abort >>
  disch_then irule >>
  simp[mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
  qexistsl_tac [`UNIV`, `d`, `ri`] >> simp[] >>
  (conj_tac >- (gen_tac >> simp[FLOOKUP_DEF] >> IF_CASES_TAC >> simp[])) >>
  (conj_tac >- metis_tac[]) >>
  (rpt strip_tac >> Cases_on `k = d`
  >- (gvs[] >> sym_tac >> irule ricf_block_edit_unchanged_fetch >>
      simp[] >> qexists_tac `bb` >> simp[]) >>
  `k < d` by decide_tac >>
  Cases_on `get_instruction bb (k + SUC t.vs_inst_idx)`
  >- (drule ricf_block_edit_EL >> gvs[get_instruction_def]) >>
  rename1 `get_instruction bb (k + SUC t.vs_inst_idx) = SOME jj'` >>
  `jj'.inst_opcode = ASSIGN` by metis_tac[] >>
  gvs[] >> sym_tac >> irule ricf_block_edit_unchanged_fetch >>
  simp[] >> qexists_tac `bb` >> simp[])
QED
