(* Reachable memory-write consumers. *)
Theory lowerDloadSafetyWriteAssembly
Ancestors
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyTaintWidth
  lowerDloadSafetyMemoryWriteEffects lowerDloadSafetyMemoryCopyEffects
  lowerDloadSafetyEmptyCopy lowerDloadSafetyValues lowerDloadSafetyRelation
  ptrDiscipline pointerConfinedDefs memLocDefs venomInst venomExecSemantics venomState finite_map list pred_set

Theorem ld_write_value_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8] /\
  inst.inst_operands = [a;Var v] ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `a = Var v` >> simp[]
QED

Theorem ld_copy_length_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [a;b;Var v] ==>
  v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `a = Var v` >> Cases_on `b = Var v` >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_write_operand_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] /\ MEM op inst.inst_operands /\
  tn.t_var = f.lf_tv /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y ==>
  (op_prov f.lf_H op = NONE ==> word_agree_except (op_taint tn op) x y) /\
  (!a. op_prov f.lf_H op = SOME a ==> ld_wordrel A (SOME a) x y)
Proof
  strip_tac >>
  `!v. op = Var v ==> ~retpc_var f.lf_fn v` by
    (gen_tac >> disch_tac >> irule ld_numeric_operand_nonopaque >>
     simp[] >> qexists_tac `inst` >> gvs[]) >>
  Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
      ld_word_agree_empty] >>
  drule_all ld_vars_value >> Cases_on `FLOOKUP f.lf_H s` >> simp[]
QED

Theorem ld_write_operand_defined:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  MEM inst (fn_insts f.lf_fn) /\ MEM op inst.inst_operands /\
  eval_operand op f.lf_tgt = SOME y ==>
  ?x. eval_operand op f.lf_src = SOME x
Proof
  strip_tac >>
  `IS_SOME (eval_operand op f.lf_src)` by
    (drule ld_vars_operand_defined >> disch_then (qspec_then `op` mp_tac) >> simp[] >>
     impl_tac >- (rpt strip_tac >> irule ld_inst_input_ir >> metis_tac[]) >>
     simp[]) >>
  Cases_on `eval_operand op f.lf_src` >> gvs[]
QED
