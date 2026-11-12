Theory lowerDloadLoadRepresentation
Ancestors
  lowerDloadMacroBoundary lowerDloadLiveScratch venomExecSemantics venomState finite_map pred_set

Theorem ld_load_first_old_lookup[local]:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC 0) t u /\ j <> a.inst_id ==>
  FLOOKUP t.vs_allocas j = FLOOKUP t0.vs_allocas j
Proof
  strip_tac >> drule_all ld_load_first_prefix >>
  disch_then (fn th => gvs[th]) >>
  Cases_on `FLOOKUP t0.vs_allocas a.inst_id`
  >- simp[update_var_def, FLOOKUP_UPDATE] >>
  PairCases_on `x` >> simp[update_var_def]
QED

Theorem ld_load_second_old_lookup[local]:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC (SUC 0)) t u /\ j <> a.inst_id ==>
  FLOOKUP t.vs_allocas j = FLOOKUP t0.vs_allocas j
Proof
  strip_tac >> drule_all ld_load_second_prefix >>
  disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_first_old_lookup) >> simp[update_var_def]
QED

Theorem ld_load_third_old_lookup[local]:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC (SUC (SUC 0))) t u /\ j <> a.inst_id ==>
  FLOOKUP t.vs_allocas j = FLOOKUP t0.vs_allocas j
Proof
  strip_tac >> drule_all ld_load_third_prefix >>
  disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_second_old_lookup) >>
  simp[write_memory_with_expansion_def]
QED

Theorem ld_load_prefix_old_lookup:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  0 < n /\ n <= 4 /\ ld_target_prefix CT [a;b;c;d] t0 un n t u /\ j <> a.inst_id ==>
  FLOOKUP t.vs_allocas j = FLOOKUP t0.vs_allocas j
Proof
  strip_tac >>
  Cases_on `n = 1`
  >- (gvs[] >> drule_all (SRULE [] ld_load_first_old_lookup) >> simp[]) >>
  Cases_on `n = 2`
  >- (gvs[] >> drule_all (SRULE [] ld_load_second_old_lookup) >> simp[]) >>
  Cases_on `n = 3`
  >- (gvs[] >> drule_all (SRULE [] ld_load_third_old_lookup) >> simp[]) >>
  `n = 4` by decide_tac >> gvs[] >>
  drule_all (SRULE [] ld_load_fourth_prefix) >> disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_third_old_lookup) >> simp[update_var_def]
QED

Theorem ld_load_prefix_live_representation:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  0 < n /\ n <= 4 /\ ld_target_prefix CT [a;b;c;d] t0 un n t u /\
  a.inst_id IN keys /\ live' SUBSET live /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt + sz <= lo \/ (?j. j NOTIN keys /\ FLOOKUP t0.vs_allocas j = SOME (bt,sz))) ==>
  (!owner bs bt sz. owner IN live' /\ ld_site_entry E owner bs bt sz ==>
    bt + sz <= lo \/ (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME (bt,sz)))
Proof
  rpt strip_tac >>
  `owner IN live` by metis_tac[SUBSET_DEF] >>
  first_x_assum (drule_all_then strip_assume_tac)
  >- simp[] >>
  disj2_tac >> qexists_tac `j` >> simp[] >>
  `j <> a.inst_id` by metis_tac[] >>
  drule_all ld_load_prefix_old_lookup >> simp[]
QED
