Theory concretizePtrLocalOrigin
Ancestors
  concretizePtrClosure concretizeAnalysisRoots allocaRemapSSA
  ptrDiscipline pointerClosure pointerConfinedDefs venomWf venomInst
  pred_set list

Theorem ptr_local_partition[local]:
  FINITE roots /\ FINITE bigroots /\ roots SUBSET bigroots /\
  v IN pointer_derived_vars fn bigroots ==>
  v IN pointer_derived_vars fn roots \/ v IN pointer_derived_vars fn (bigroots DIFF roots)
Proof
  strip_tac >> drule_all ptr_derived_root_witness >> strip_tac >>
  Cases_on `r IN roots`
  >- (disj1_tac >>
      `pointer_derived_vars fn {r} SUBSET pointer_derived_vars fn roots` by
        (irule ptr_derived_mono >> simp[]) >> metis_tac[SUBSET_DEF]) >>
  disj2_tac >>
  `pointer_derived_vars fn {r} SUBSET pointer_derived_vars fn (bigroots DIFF roots)` by
    (irule ptr_derived_mono >> simp[]) >> metis_tac[SUBSET_DEF]
QED

Theorem ptr_pure_local_phi_input:
  fn_ptr_ok P fn /\ ssa_form fn /\
  L = pointer_derived_vars fn (alloca_roots fn) /\
  X = pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn) /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_opcode = PHI /\ MEM out inst.inst_outputs /\
  out IN L /\ out NOTIN X /\ MEM (Var v) inst.inst_operands ==>
  v IN L DIFF X
Proof
  strip_tac >>
  `alloca_roots fn SUBSET ptr_roots P fn` by
    simp[ptr_roots_def, SUBSET_DEF] >>
  `FINITE (alloca_roots fn)` by
    metis_tac[SUBSET_FINITE, ptr_roots_finite] >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
  `?u. MEM (Var u) inst.inst_operands /\ u IN L` by
    (spose_not_then assume_tac >>
     `!op v. MEM op inst.inst_operands /\ op = Var v ==>
        v NOTIN pointer_derived_vars fn (alloca_roots fn)` by metis_tac[] >>
     `~is_alloca_op inst.inst_opcode` by simp[is_alloca_op_def] >>
     `alloca_roots fn SUBSET alloca_roots fn` by simp[] >>
     drule_all no_pv_outputs_from_no_pv_inputs >> metis_tac[]) >>
  `pointer_derived_vars fn (alloca_roots fn) SUBSET fn_pv P fn` by
    (simp[fn_pv_def] >> irule ptr_derived_mono >> simp[ptr_roots_finite]) >>
  `u IN fn_pv P fn` by metis_tac[SUBSET_DEF] >>
  `v IN fn_pv P fn` by
    (`phi_pv_all_var fn (ptr_roots P fn)` by gvs[fn_ptr_ok_def] >>
     qpat_x_assum `phi_pv_all_var _ _` mp_tac >>
     simp[phi_pv_all_var_def] >>
     disch_then (qspecl_then [`bb`,`inst`] mp_tac) >>
     simp[GSYM fn_pv_def] >> metis_tac[]) >>
  `v NOTIN X` by
    (strip_tac >>
     `out IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)` by
       (irule pointer_derived_vars_closed >>
        simp[FINITE_DIFF, ptr_roots_finite] >>
        qexistsl [`inst`,`v`] >> gvs[is_pointer_preserving_op_def]) >> metis_tac[]) >>
  `v IN L \/ v IN X` by
    (gvs[fn_pv_def] >>
     drule_at (Pos last) ptr_local_partition >>
     disch_then (qspec_then `alloca_roots fn` mp_tac) >>
     simp[ptr_roots_finite]) >> simp[] >> metis_tac[]
QED
