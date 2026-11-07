Theory concretizeAnalysisExclusiveWriters
Ancestors
  concretizeAnalysisExclusiveSources concretizeAnalysisRoots pointerClosure
  allocaRemapSSA removeUnusedSsaProofs phiWellFormed execEquivParamBase venomWf ptrDiscipline pointerConfinedDefs venomInst pred_set list

Definition allocation_exclusive_def:
  allocation_exclusive P fn v <=>
    v IN pointer_derived_vars fn (alloca_roots fn) /\
    v NOTIN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)
End

Theorem alloca_derived_writer[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs /\
  v IN pointer_derived_vars fn (alloca_roots fn) ==>
  inst.inst_opcode = ALLOCA \/
  (is_pointer_preserving_op inst.inst_opcode /\
   ?u. MEM (Var u) inst.inst_operands /\
       u IN pointer_derived_vars fn (alloca_roots fn))
Proof
  strip_tac >>
  `FINITE (alloca_roots fn)` by
    (irule SUBSET_FINITE >> qexists `ptr_roots P fn` >>
     simp[ptr_roots_finite, ptr_roots_def, SUBSET_DEF]) >>
  gvs[pointer_derived_vars_def] >>
  drule pointer_use_vars_mem_char >> strip_tac
  >- (gvs[MEM_SET_TO_LIST, alloca_roots_def, inst_output_def, AllCaseEqs()] >>
      `inst = inst'` by (irule ssa_unique_output >> metis_tac[MEM]) >> gvs[])
  >> `inst = inst'` by
    (irule ssa_unique_output >> metis_tac[mem_fn_insts_intro]) >>
  gvs[] >> metis_tac[]
QED

Theorem allocation_exclusive_writer:
  ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs /\
  allocation_exclusive P fn v ==>
  inst.inst_outputs = [v] /\
  (inst.inst_opcode = ALLOCA \/
   (is_pointer_preserving_op inst.inst_opcode /\
    ?u. MEM (Var u) inst.inst_operands /\ allocation_exclusive P fn u))
Proof
  strip_tac >>
  `v IN pointer_derived_vars fn (alloca_roots fn)` by gvs[allocation_exclusive_def] >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  drule_all alloca_derived_writer >> strip_tac
  >- (gvs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[] >>
      Cases_on `t` >> gvs[])
  >> `inst.inst_outputs = [v]` by
    (Cases_on `inst.inst_opcode` >> gvs[is_pointer_preserving_op_def, inst_wf_def] >>
     Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  simp[] >> disj2_tac >> simp[] >> qexists `u` >>
  gvs[allocation_exclusive_def] >>
  irule ptr_derived_backward_exclusion >> simp[ptr_roots_finite] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  qexistsl [`bb`, `inst`, `v`] >> simp[]
QED

Theorem allocation_exclusive_phi_source:
  ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs /\
  allocation_exclusive P fn v /\ inst.inst_opcode = PHI /\
  resolve_phi lbl inst.inst_operands = SOME op ==>
    ?u. op = Var u /\ allocation_exclusive P fn u
Proof
  strip_tac >> drule_all allocation_exclusive_writer >> strip_tac >> gvs[] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  drule_all resolve_phi_well_formed >> strip_tac >> gvs[] >>
  `MEM (Var var) inst.inst_operands` by metis_tac[resolve_phi_MEM] >>
  simp[allocation_exclusive_def] >> conj_tac
  >- (irule phi_allocation_exclusive_inputs >>
      gvs[allocation_exclusive_def] >> metis_tac[MEM])
  >> irule ptr_derived_backward_exclusion >> simp[ptr_roots_finite] >>
  gvs[allocation_exclusive_def] >> metis_tac[MEM]
QED

Theorem allocation_exclusive_opcode:
  ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM v inst.inst_outputs /\ allocation_exclusive P fn v ==>
  MEM inst.inst_opcode [ALLOCA; ADD; SUB; ASSIGN; PHI]
Proof
  strip_tac >> drule_all allocation_exclusive_writer >> strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode` >> gvs[is_pointer_preserving_op_def]
QED
