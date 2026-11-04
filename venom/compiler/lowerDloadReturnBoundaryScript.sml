Theory lowerDloadReturnBoundary
Ancestors
  lowerDloadProvenanceSupport lowerDloadReachableDiscipline
  lowerDloadPairedBoundary lowerDloadOwnership ptrDiscipline memLocDefs venomExecSemantics
  venomState venomInst finite_map pred_set list pointerConfinedDefs

Theorem ld_ret_operand_scalar:
  fn_ptr_ok P fn /\ MEM i (fn_insts fn) /\ i.inst_opcode = RET /\
  FDOM AG SUBSET fn_pv P fn /\ taint_ok fn tn i s /\
  MEM op i.inst_operands ==>
  ld_op_prov AG op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) i` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by
    (drule ld_taint_operand_clean >> simp[]) >>
  simp[] >> Cases_on `op` >> simp[ld_op_prov_def] >>
  rename1 `MEM (Var v) i.inst_operands` >>
  `v NOTIN fn_pv P fn` by
    (qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_read_ops_def, mem_write_ops_def] >> metis_tac[]) >>
  metis_tac[FLOOKUP_DEF, SUBSET_DEF]
QED

Theorem ld_owned_operands_clean:
  !ops. ld_owned_vars V E AG BH tn un s t /\
    (!op. MEM op ops ==> (!v. op = Var v ==> v IN V) /\
      ld_op_prov AG op = NONE /\ op_taint tn op = {}) ==>
    eval_operands ops s = eval_operands ops t
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by
    (irule ld_owned_operand_clean >> metis_tac[]) >>
  `eval_operands ops s = eval_operands ops t` by
    (first_x_assum irule >> metis_tac[]) >> simp[]
QED

Theorem ld_ret_operands_equal:
  fn_ptr_ok P fn /\ MEM i (fn_insts fn) /\ i.inst_opcode = RET /\
  FDOM AG SUBSET fn_pv P fn /\ taint_ok fn tn i s /\
  ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) ==>
  eval_operands i.inst_operands s = eval_operands i.inst_operands t
Proof
  strip_tac >> irule ld_owned_operands_clean >> simp[] >>
  rpt strip_tac >> metis_tac[ld_ret_operand_scalar]
QED

Theorem ld_annotated_ret_operands_equal:
  ptr_discipline lo ctx vs0 /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn i s /\
  i.inst_opcode = RET /\ ld_owned_vars V E AG BH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) ==>
  eval_operands i.inst_operands s = eval_operands i.inst_operands t
Proof
  strip_tac >>
  `taint_ok fn tn i s` by metis_tac[ld_annotated_taint_ok] >>
  qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
  simp[ptr_discipline_def, EVERY_MEM] >> strip_tac >>
  `FDOM AG SUBSET fn_pv P fn` by metis_tac[ld_annotated_prov_support] >>
  `MEM fn ctx.ctx_functions` by metis_tac[ld_annotated_fn_member] >>
  `active_inst fn i s` by metis_tac[ld_annotated_active_inst] >>
  `MEM i (fn_insts fn)` by
    (gvs[contextCodegenRelTheory.active_inst_def,
         fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  irule ld_ret_operands_equal >> metis_tac[]
QED
