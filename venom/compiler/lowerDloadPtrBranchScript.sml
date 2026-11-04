Theory lowerDloadPtrBranch
Ancestors
  lowerDloadPtrAggregate lowerDloadPtrRel lowerDloadPtrCall
  lowerDloadPtrScalar lowerDloadPtrPhi lowerDloadPtrStatic
  ptrDiscipline pointerConfinedDefs venomExecSemantics venomState venomInst
  memLocDefs finite_map list pred_set words

Theorem dload_boundary_core_jump[local]:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_boundary_core lo fs V Ws PG PH G H tn un
    (jump_to lbl s) (jump_to lbl t) cs ds
Proof
  simp[dload_boundary_core_def, jump_to_def,
    dload_table_stack_def, dload_vars_match_def, dload_memory_match_def,
    dload_shared_store_def, dload_equal_environment_def, lookup_var_def,
    venom_state_component_equality] >> strip_tac >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!k. k < LENGTH fs ==> _`
        (qspec_then `k` mp_tac) >> Cases_on `k` >> gvs[]) >>
  gvs[] >> metis_tac[]
QED

Theorem branch_operand_clean[local]:
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  gvs[MEM, ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem branch_step_transport[local]:
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel Ct i t = OK t1 ==>
  ?lbl. t1 = jump_to lbl t /\ step_inst fuel Cs i s = OK (jump_to lbl s)
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[MEM]
QED

Theorem dload_boundary_core_branch:
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> ~retpc_var f v /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1 lbl. step_inst fuel Cs i s = OK s1 /\
    s1 = jump_to lbl s /\ t1 = jump_to lbl t /\
    s1.vs_current_bb = t1.vs_current_bb /\ s1.vs_prev_bb = t1.vs_prev_bb /\
    (s1.vs_halted <=> t1.vs_halted) /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s1 t1 cs ds
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_labels = t.vs_labels /\ s.vs_current_bb = t.vs_current_bb /\
   (s.vs_halted <=> t.vs_halted)` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `dload_vars_match fs {v | ~retpc_var f v} G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `op_prov G op = NONE /\ op_taint tn op = {}` by
       (drule_all branch_operand_clean >> simp[]) >>
     `!v. op = Var v ==> v IN {v | ~retpc_var f v}` by (simp[] >> metis_tac[]) >>
     `eval_operand op s = NONE <=> eval_operand op t = NONE` by
       (drule eval_operand_definedness >>
        disch_then (qspec_then `op` mp_tac) >>
        (impl_tac >- metis_tac[]) >> simp[]) >>
     drule_all scalar_operand_equal >> simp[]) >>
  drule_all branch_step_transport >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  drule dload_boundary_core_jump >>
  disch_then (qspec_then `lbl` assume_tac) >>
  qexistsl [`jump_to lbl s`,`lbl`] >> gvs[jump_to_def, lookup_var_def]
QED
