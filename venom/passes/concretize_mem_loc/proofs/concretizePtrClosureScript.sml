Theory concretizePtrClosure
Ancestors
  pointerClosure pointerConfinedDefs venomInst pred_set list While
  removeUnusedSsaProofs

Theorem ptr_closure_step_subset[local]:
  (!inst v out. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var v) inst.inst_operands /\ v IN target /\ MEM out inst.inst_outputs ==>
    out IN target) /\ set vars SUBSET target /\
  pointer_use_step_step fn vars = SOME next ==> set next SUBSET target
Proof
  simp[pointer_use_step_step_def, AllCaseEqs(), SUBSET_DEF,
       pointer_use_step_membership, MEM_FILTER] >>
  rpt strip_tac >> gvs[MEM_FILTER, pointer_use_step_membership] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ptr_closure_loop_subset[local]:
  (!inst v out. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var v) inst.inst_operands /\ v IN target /\ MEM out inst.inst_outputs ==>
    out IN target) /\ set vars SUBSET target /\
  OWHILE ISL (pointer_closure_next fn) (INL vars) = SOME (INR result) ==>
  set result SUBSET target
Proof
  strip_tac >>
  `(\s. case s of INL vs => set vs SUBSET target | INR vs => set vs SUBSET target)
      (INR result)` suffices_by simp[] >>
  irule OWHILE_INV_IND >>
  qexistsl [`ISL`, `pointer_closure_next fn`, `INL vars`] >>
  simp[] >> rpt gen_tac >> Cases_on `x` >> simp[pointer_closure_next_def] >>
  strip_tac >> Cases_on `pointer_use_step_step fn x'` >> simp[] >>
  metis_tac[ptr_closure_step_subset]
QED

Theorem ptr_derived_least:
  FINITE roots /\ roots SUBSET target /\
  (!inst v out. MEM inst (fn_insts fn) /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var v) inst.inst_operands /\ v IN target /\ MEM out inst.inst_outputs ==>
    out IN target) ==>
  pointer_derived_vars fn roots SUBSET target
Proof
  strip_tac >>
  qspec_then `SET_TO_LIST roots` strip_assume_tac pointer_closure_terminates >>
  `set result SUBSET target` by
    (irule ptr_closure_loop_subset >> goal_assum (drule_at Any) >>
     simp[SET_TO_LIST_INV] >> metis_tac[]) >>
  gvs[pointer_derived_vars_def, pointer_use_vars_def,
      GSYM pointer_closure_next_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem ptr_derived_mono:
  FINITE roots /\ FINITE roots' /\ roots SUBSET roots' ==>
  pointer_derived_vars fn roots SUBSET pointer_derived_vars fn roots'
Proof
  rpt strip_tac >> irule ptr_derived_least >> simp[] >> conj_tac
  >- metis_tac[pointer_derived_vars_closed]
  >> metis_tac[pointer_derived_vars_roots, SUBSET_TRANS]
QED

Theorem ptr_derived_root_witness:
  FINITE R /\ v IN pointer_derived_vars fn R ==>
  ?r. r IN R /\ v IN pointer_derived_vars fn {r}
Proof
  strip_tac >>
  `pointer_derived_vars fn R SUBSET
    {u | ?r. r IN R /\ u IN pointer_derived_vars fn {r}}` suffices_by
    (simp[SUBSET_DEF] >> metis_tac[]) >>
  irule ptr_derived_least >> simp[SUBSET_DEF] >>
  conj_tac
  >- (rpt strip_tac >> qexists `r` >> simp[] >>
      irule pointer_derived_vars_closed >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> qexists `x` >> simp[] >>
  mp_tac (Q.INST [`roots` |-> `{x}`, `fn` |-> `fn`] pointer_derived_vars_roots) >>
  simp[SUBSET_DEF]
QED
