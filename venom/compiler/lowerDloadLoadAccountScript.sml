Theory lowerDloadLoadAccount
Ancestors
  lowerDloadAllocation lowerDloadMacroBoundary venomExecSemantics venomState finite_map words

Theorem ld_load_first_account[local]:
  ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC 0) t u ==>
  ld_alloc_account keys d0 (a.inst_id INSERT A) s t
Proof
  strip_tac >> drule_all ld_load_first_prefix >>
  disch_then (fn th => gvs[th]) >>
  qmatch_goalsub_abbrev_tac `r with vs_inst_idx := _` >>
  irule ld_alloc_account_transport >> qexistsl_tac [`s`,`r`] >> simp[] >>
  irule ld_alloc_account_scratch >> simp[] >> qexists_tac `t0` >>
  simp[exec_alloca_def, Abbr `r`] >>
  Cases_on `FLOOKUP t0.vs_allocas a.inst_id` >> gvs[dimword_def] >>
  PairCases_on `x` >> gvs[]
QED

Theorem ld_load_second_account[local]:
  ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC (SUC 0)) t u ==>
  ld_alloc_account keys d0 (a.inst_id INSERT A) s t
Proof
  strip_tac >> drule_all ld_load_second_prefix >>
  disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_first_account) >> strip_tac >>
  irule ld_alloc_account_transport >> qexistsl_tac [`s`,`r`] >>
  simp[update_var_def]
QED

Theorem ld_load_third_account[local]:
  ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC (SUC (SUC 0))) t u ==>
  ld_alloc_account keys d0 (a.inst_id INSERT A) s t
Proof
  strip_tac >> drule_all ld_load_third_prefix >>
  disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_second_account) >> strip_tac >>
  irule ld_alloc_account_transport >> qexistsl_tac [`s`,`r`] >>
  simp[write_memory_with_expansion_def]
QED

Theorem ld_load_prefix_account:
  ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\ (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  0 < n /\ n <= 4 /\ ld_target_prefix CT [a;b;c;d] t0 un n t u ==>
  ld_alloc_account keys d0 (a.inst_id INSERT A) s t
Proof
  strip_tac >>
  Cases_on `n = 1`
  >- (gvs[] >> drule_all (SRULE [] ld_load_first_account) >> simp[]) >>
  Cases_on `n = 2`
  >- (gvs[] >> drule_all (SRULE [] ld_load_second_account) >> simp[]) >>
  Cases_on `n = 3`
  >- (gvs[] >> drule_all (SRULE [] ld_load_third_account) >> simp[]) >>
  `n = 4` by decide_tac >> gvs[] >>
  drule_all (SRULE [] ld_load_fourth_prefix) >> disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_third_account) >> strip_tac >>
  irule ld_alloc_account_transport >> qexistsl_tac [`s`,`r`] >>
  simp[update_var_def]
QED

Theorem ld_load_completed_account:
  ld_alloc_account keys d0 A s t0 /\ a.inst_id IN keys /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\ (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix CT [a;b;c;d] t0 un 4 t u /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  step_inst fuel CS inst s = OK z ==>
  ld_alloc_account keys d0 (a.inst_id INSERT A) z t
Proof
  strip_tac >> gvs[] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `4`] ld_load_prefix_account)) >> strip_tac >>
  irule ld_alloc_account_transport >> qexistsl_tac [`s`,`t`] >> simp[] >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  simp[update_var_def]
QED
