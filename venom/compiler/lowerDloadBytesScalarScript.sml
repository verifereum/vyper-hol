Theory lowerDloadBytesScalar
Ancestors
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadPairedBoundary ptrDiscipline pointerConfinedDefs memLocDefs
  venomInst list pred_set o1PassContract contextCodegenRel

Theorem ld_bytes_scalars_not_pointer:
  ptr_use_ok P pv i /\ i.inst_opcode = DLOADBYTES /\
  i.inst_operands = [dst;off;sz] ==>
  (!v. off = Var v ==> v NOTIN pv) /\
  (!v. sz = Var v ==> v NOTIN pv)
Proof
  simp[ptr_use_ok_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  Cases_on `dst = Var v` >> simp[] >>
  Cases_on `off = Var v` >> simp[] >>
  Cases_on `sz = Var v` >> simp[]
QED

Theorem ld_reachable_bytes_scalars:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\
  (!f. MEM f CS.ctx_functions ==> fn_ptr_ok P f) /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  ~in_revert_forward fn s /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN V) ==>
  eval_operand off s = eval_operand off t /\
  eval_operand sz s = eval_operand sz t
Proof
  strip_tac >>
  `MEM fn CS.ctx_functions` by
    (drule_all ld_annotated_fn_member >> simp[]) >>
  `MEM i (fn_insts fn)` by
    (drule ld_annotated_active_inst >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM]) >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) i` by metis_tac[fn_ptr_ok_def] >>
  drule_all ld_bytes_scalars_not_pointer >> strip_tac >>
  `ld_op_prov AG off = NONE` by
    metis_tac[ld_annotated_scalar_prov] >>
  `ld_op_prov AG sz = NONE` by
    metis_tac[ld_annotated_scalar_prov] >>
  drule_all ld_annotated_taint_ok >> strip_tac >>
  `op_taint tn off = {}` by
    (irule ld_taint_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  `op_taint tn sz = {}` by
    (irule ld_taint_operand_clean >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (drule ld_owned_operand_clean >>
      disch_then (qspec_then `off` mp_tac) >> simp[] >> metis_tac[]) >>
  drule ld_owned_operand_clean >>
  disch_then (qspec_then `sz` mp_tac) >> simp[] >> metis_tac[]
QED
