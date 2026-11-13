Theory concretizePtrWritePurity
Ancestors concretizePtrWriteClassification ptrDiscipline memLocDefs
  pointerConfinedDefs finite_map list pred_set

Theorem ptr_write_max_size_untainted:
  taint_ok fn tn inst s /\ mem_write_ops inst = SOME ops /\
  ops.iao_max_size = SOME sizeop ==> op_taint tn sizeop = {}
Proof
  Cases_on `inst.inst_opcode` >>
  simp[mem_write_ops_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[taint_ok_def] >>
  simp[op_taint_def] >> metis_tac[op_taint_def]
QED

Theorem ptr_write_max_size_not_pointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop ==>
  !v. sizeop = Var v ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `fn_ptr_ok P fn` kall_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[mem_write_ops_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ptr_write_max_size_no_provenance:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  (!v. v IN FDOM TG ==> v IN fn_pv P fn) ==>
  op_prov TG sizeop = NONE
Proof
  strip_tac >>
  `!v. sizeop = Var v ==> v NOTIN fn_pv P fn` by
    (gen_tac >> strip_tac >> irule ptr_write_max_size_not_pointer >>
     metis_tac[]) >>
  Cases_on `sizeop` >> gvs[op_prov_def] >>
  metis_tac[flookup_thm]
QED

Theorem ptr_mstore_value_not_pointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [a;v] ==>
  !x. v = Var x ==> x NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `fn_ptr_ok P fn` kall_tac >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >> strip_tac >> gvs[]
QED

Theorem ptr_mstore_value_no_provenance:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [a;v] /\
  (!x. x IN FDOM TG ==> x IN fn_pv P fn) ==>
  op_prov TG v = NONE
Proof
  strip_tac >>
  `!x. v = Var x ==> x NOTIN fn_pv P fn` by
    (gen_tac >> strip_tac >> irule ptr_mstore_value_not_pointer >> metis_tac[]) >>
  Cases_on `v` >> gvs[op_prov_def] >> metis_tac[flookup_thm]
QED
