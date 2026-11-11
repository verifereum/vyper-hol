Theory concretizeAnalysisExclusiveSources
Ancestors concretizeAnalysisRoots pointerClosure ptrDiscipline
  pointerConfinedDefs venomInst memLocDefs pred_set list

Theorem alloca_roots_ptr_subset[local]:
  alloca_roots fn SUBSET ptr_roots P fn
Proof simp[ptr_roots_def, SUBSET_DEF]
QED

Theorem alloca_roots_finite[local]:
  FINITE (alloca_roots fn)
Proof
  irule SUBSET_FINITE >> qexists `ptr_roots P fn` >>
  simp[ptr_roots_finite, alloca_roots_ptr_subset]
QED

Theorem fn_pv_root_decomposition:
  fn_pv P fn = pointer_derived_vars fn (alloca_roots fn) UNION
    pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)
Proof
  simp[fn_pv_def, GSYM ptr_derived_union,
       alloca_roots_finite, ptr_roots_finite] >>
  AP_TERM_TAC >>
  mp_tac alloca_roots_ptr_subset >> simp[EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem phi_allocation_exclusive_inputs:
  fn_ptr_ok P fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_opcode = PHI /\ MEM out inst.inst_outputs /\
  out NOTIN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn) /\
  (?u. MEM (Var u) inst.inst_operands /\
       u IN pointer_derived_vars fn (alloca_roots fn)) /\
  MEM (Var v) inst.inst_operands ==>
  v IN pointer_derived_vars fn (alloca_roots fn)
Proof
  strip_tac >>
  `v NOTIN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)` by
    (irule ptr_derived_backward_exclusion >>
     simp[ptr_roots_finite] >> goal_assum (drule_at Any) >>
     simp[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `u IN fn_pv P fn` by simp[fn_pv_root_decomposition] >>
  `v IN fn_pv P fn` by
    (gvs[fn_ptr_ok_def, phi_pv_all_var_def, fn_pv_def] >> metis_tac[]) >>
  gvs[fn_pv_root_decomposition]
QED

Theorem write_allocation_exclusive:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  v IN pointer_derived_vars fn (alloca_roots fn) ==>
  v NOTIN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)
Proof
  simp[fn_ptr_ok_def] >> metis_tac[]
QED
