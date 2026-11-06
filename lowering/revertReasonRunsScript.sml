(* Ordinary execution witnesses for the shared revert encoder chunks. *)
Theory revertReasonRuns
Ancestors
  revertReasonLayout revertReasonCopyPtr allocaSiteResource fragExec exprLoweringProps
  venomExecSemantics venomState venomInst words finite_map arithmetic

Theorem revert_reason_copy_run:
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  (!k. k < 4 ==> src <> STRING #"%" (toString (v+k)) /\
                    dst <> STRING #"%" (toString (v+k))) ==>
  ?t. run_inst_seq (revert_reason_copy id v (Var dst) (Var src)) s = OK t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `?t. run_inst_seq (revert_reason_copy id v (Var dst) (Var src)) s = OK t`
    suffices_by metis_tac[revert_reason_copy_allocation_frame] >>
  map_every (fn k => qpat_assum `!k. k < 4 ==> _`
    (qspec_then k assume_tac)) [`0`,`1`,`2`,`3`] >>
  gvs[] >>
  pure_rewrite_tac[revert_reason_copy_def] >>
  simp[Once run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_read1_def, eval_operand_def] >>
  simp[Once run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[lookup_var_def] >> simp[run_inst_seq_def]
QED

Theorem revert_reason_prefix_run:
  ?t. run_inst_seq (revert_reason_prefix id v ms) s = OK t
Proof
  `?s1 a. step_inst_base
     (mk_inst id ALLOCA [Lit (n2w (64+ms))]
       [STRING #"%" (toString v)]) s = OK s1 /\
     lookup_var (STRING #"%" (toString v)) s1 = SOME a` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas id` >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     PairCases_on `x` >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  pure_rewrite_tac[revert_reason_prefix_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_write2_def, eval_operand_def] >>
  simp[Once run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_pure2_def, eval_operand_def,
       mstore_def, lookup_var_def] >>
  simp[run_inst_seq_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s1.vs_allocas (id+3)` >> simp[] >>
  PairCases_on `x` >> simp[]
QED
