Theory lowerDloadOrdinaryAllocation
Ancestors
  lowerDloadAllocation lowerDloadPairedBoundary venomExecSemantics
  venomState venomInst finite_map pred_set list words

Theorem ld_owned_alloca_witness_backward:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  ld_alloc_account keys d0 A s t /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ ld_op_prov AG op = NONE /\
  op_taint tn op = {} /\ step_inst fuelT CT i t = OK t' ==>
  ?s' n bs bt sz.
    step_inst fuelS CS i s = OK s' /\ ld_alloc_account keys d0 A s' t' /\
    eval_operand op s = SOME n /\ eval_operand op t = SOME n /\
    FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
    FLOOKUP t'.vs_allocas i.inst_id = SOME (bt,sz) /\
    lookup_var out s' = SOME (n2w bs) /\
    lookup_var out t' = SOME (n2w bt) /\
    bs <= bt /\ bt <= bs + d0 + 32 * CARD A
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[] >> Cases_on `op` >> simp[] >> strip_tac >>
  rename1 `exec_alloca i t n = OK t'` >>
  `?s'. exec_alloca i s n = OK s'` by
    (simp[exec_alloca_def] >> Cases_on `FLOOKUP s.vs_allocas i.inst_id` >>
     simp[] >> PairCases_on `x` >> simp[]) >>
  `ld_alloc_account keys d0 A s' t'` by
    (drule_all (SRULE [] (Q.INST [`j` |-> `i`] ld_alloc_account_ordinary)) >> simp[]) >>
  `?bs bt sz.
    FLOOKUP s'.vs_allocas i.inst_id = SOME (bs,sz) /\
    FLOOKUP t'.vs_allocas i.inst_id = SOME (bt,sz) /\
    lookup_var out s' = SOME (n2w bs) /\
    lookup_var out t' = SOME (n2w bt) /\
    ld_ptr_rel bs bt (n2w bs) (n2w bt) /\
    bt <= bs + d0 + 32 * CARD A` by
    (drule_all (SRULE [] (Q.INST [`j` |-> `i`] ld_alloc_account_outputs)) >> simp[]) >>
  `bs <= bt` by
    (drule_all ld_alloc_account_old_entry >> strip_tac >> gvs[]) >>
  qexistsl [`s'`, `n`, `bs`, `bt`, `sz`] >>
  simp[eval_operand_def, step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[]
QED

Theorem ld_owned_alloca_account_backward:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [op] /\
  i.inst_outputs = [out] /\ i.inst_id NOTIN keys /\
  ld_alloc_account keys d0 A s t /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. op = Var v ==> v IN V) /\ ld_op_prov AG op = NONE /\
  op_taint tn op = {} /\ step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\ ld_alloc_account keys d0 A s' t'
Proof
  metis_tac[ld_owned_alloca_witness_backward]
QED
