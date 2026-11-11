Theory lowerDloadLoadValues
Ancestors
  lowerDloadCompletedOutput lowerDloadBytesScalar lowerDloadDefs lowerDloadMacroBoundary
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadPairedBoundary ptrDiscipline pointerConfinedDefs memLocDefs
  venomInst list pred_set o1PassContract contextCodegenRel

Theorem ld_load_offset_not_pointer[local]:
  ptr_use_ok P pv i /\ i.inst_opcode = DLOAD /\ i.inst_operands = [off] ==>
  (!v. off = Var v ==> v NOTIN pv)
Proof
  simp[ptr_use_ok_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]
QED

Theorem ld_reachable_load_owned:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\ a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\ av NOTIN V /\ bv NOTIN V /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  c.inst_outputs = [] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t0 /\
  (!v. off = Var v ==> v IN V) /\
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn inst s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  ~in_revert_forward fn s /\ dload_offset_ok CS fn inst s /\
  code_layout_valid s /\ t0.vs_code = s.vs_code /\
  eval_operand (Label "code_end") t0 =
    SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
  ld_target_prefix CT [a;b;c;d] t0 un (SUC (SUC (SUC (SUC 0)))) t u ==>
  ?z. step_inst fuel CS inst s = OK z /\
    ld_owned_vars V E (ld_set_prov AG [out] NONE)
      (ld_set_prov (ld_set_prov AH [bv] NONE) [out] NONE)
      (step_taint inst s z tn) u z t
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by
    (drule_all ld_annotated_fn_member >> simp[]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  `!v. off = Var v ==> v NOTIN fn_pv P fn` by
    metis_tac[ld_load_offset_not_pointer] >>
  `ld_op_prov AG off = NONE` by metis_tac[ld_annotated_scalar_prov] >>
  drule_all ld_annotated_taint_ok >> strip_tac >>
  `op_taint tn off = {}` by
    (irule ld_taint_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `!v. off = Var v ==> v <> av` by metis_tac[] >>
  `?x. eval_operand off t0 = SOME x` by
    (drule_all ld_load_fourth_prefix >> disch_then (fn th => gvs[th]) >>
     drule_all (SRULE [] ld_load_third_prefix) >> disch_then (fn th => gvs[th]) >>
     drule_all (SRULE [] ld_load_second_values) >> metis_tac[]) >>
  `eval_operand off s = SOME x` by metis_tac[ld_owned_operand_clean] >>
  `w2n x + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256)` by
    metis_tac[dload_offset_ok_def] >>
  drule_all ld_load_completed_owned >> simp[]
QED
