Theory lowerDloadResidualCopy
Ancestors
  lowerDloadNormalExisting lowerDloadNormalTransport lowerDloadCleanCopy
  lowerDloadSharedState lowerDloadMemoryExecution lowerDloadCopyCertificate
  lowerDloadEffectTransport venomExecSemantics venomState ptrDiscipline
  list words pred_set vfmState venomInst memLocDefs codegenRel

(* The payload is obtained from the shared environment, never assumed equal. *)
Theorem ld_payload_copy_execution_backward:
  MEM i.inst_opcode [CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                     else [dst;off;sz]) /\
  ld_shared_state tn un s t /\
  eval_operand dst s = SOME p /\ eval_operand dst t = SOME q /\
  eval_operand off s = SOME r /\ eval_operand off t = SOME r /\
  eval_operand sz s = SOME n /\ eval_operand sz t = SOME n /\
  (i.inst_opcode = EXTCODECOPY ==>
    eval_operand addr s = SOME a /\ eval_operand addr t = SOME a) /\
  step_inst fuelT CT i t = OK t' ==>
  ?bs. LENGTH bs = w2n n /\
    step_inst fuelS CS i s = OK (write_memory_with_expansion (w2n p) bs s) /\
    t' = write_memory_with_expansion (w2n q) bs t
Proof
  strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  `!a. (lookup_account a s.vs_accounts).code =
       (lookup_account a t.vs_accounts).code` by
    (drule ld_shared_state_nonstorage >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `a'` mp_tac) >>
     simp[lookup_account_def] >> disch_tac >>
     qsuff_tac `(s.vs_accounts a' with storage := (t.vs_accounts a').storage).code =
       (t.vs_accounts a').code` >- simp[] >> AP_TERM_TAC >> simp[]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n p) payload s` >>
  qexists_tac `payload` >> simp[Abbr `payload`, LENGTH_TAKE]
QED

Theorem ld_payload_copy_taint:
  MEM i.inst_opcode [CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY] /\
  i.inst_operands = (if i.inst_opcode = EXTCODECOPY then [addr;dst;off;sz]
                     else [dst;off;sz]) /\
  eval_operand dst s = SOME p /\ eval_operand sz s = SOME n /\
  eval_operand off s = SOME r /\
  (i.inst_opcode = EXTCODECOPY ==> eval_operand addr s = SOME a) /\
  (s' with vs_memory := s.vs_memory) = s ==>
  (step_taint i s s' tn).t_mem =
    tn.t_mem DIFF {a | w2n p <= a /\ a < w2n p + w2n n} /\
  (step_taint i s s' tn).t_stor = tn.t_stor /\
  (step_taint i s s' tn).t_trans = tn.t_trans /\
  (step_taint i s s' tn).t_imm = tn.t_imm
Proof
  strip_tac >> dxrule ld_memory_restore_normalize >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  gvs[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
      mem_taint_def, new_site_bytes_def, step_writes_def,
      source_memory_write_ranges_def, sized_source_write_range_def,
      written_taint_def, range_bytes_def, finite_mapTheory.FLOOKUP_DEF,
      EXTENSION, SF CONJ_ss] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
