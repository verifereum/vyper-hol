Theory lowerDloadPtrIdentity
Ancestors lowerDloadPtrBlockEntry lowerDloadPtrPhi lowerDloadPtrScalar lowerDloadPtrOrdinary lowerDloadPtrAggregate
  lowerDloadPtrRel ptrDiscipline venomExecSemantics venomState venomInst
  unitShapeDefs venomWf o1PassContract codegenRel memLocDefs pointerConfinedDefs
  finite_map list pred_set

Theorem identity_arity:
  fn_inst_wf f /\ MEM i (fn_insts f) /\
  MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] ==>
  i.inst_outputs = []
Proof
  simp[fn_inst_wf_def, fn_insts_def,
    o1PassContractTheory.fn_insts_blocks_MEM] >>
  strip_tac >> first_x_assum drule >> disch_then drule >>
  gvs[inst_wf_def]
QED

Theorem identity_operand_clean[local]:
  MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\
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

Theorem identity_step_transport[local]:
  MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel Ct i t = OK t' ==>
  t'=t /\ step_inst fuel Cs i s = OK s
Proof
  strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[MEM]
QED

Theorem identity_ghost_updates[local]:
  MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\
  i.inst_outputs = [] ==>
  step_prov PG G i s = G /\ step_taint i s s tn = tn
Proof
  strip_tac >>
  `written_taint tn i s = {}` by
    (irule written_taint_opcode_exclusion >> gvs[MEM]) >>
  gvs[MEM] >>
  simp[step_prov_def, set_prov_def, step_taint_def, DRESTRICT_UNIV,
    set_var_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, range_bytes_def,
    source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem dload_boundary_core_identity:
  MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\ i.inst_outputs = [] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s'=s /\ t'=t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `op_prov G op = NONE /\ op_taint tn op = {}` by
       (drule_all identity_operand_clean >> simp[]) >>
     `!v. op = Var v ==> v IN V` by metis_tac[] >>
     `eval_operand op s = NONE <=> eval_operand op t = NONE` by
       (drule eval_operand_definedness >>
        disch_then (qspec_then `op` mp_tac) >>
        (impl_tac >- metis_tac[]) >> simp[]) >>
     drule_all scalar_operand_equal >> simp[]) >>
  drule_all identity_step_transport >>
  disch_then (qspec_then `Cs` strip_assume_tac) >> gvs[] >>
  `step_prov PG G i s = G /\ step_taint i s s tn = tn` by
    (irule identity_ghost_updates >> simp[]) >>
  `step_prov PH H i t = H /\ step_taint i t t un = un` by
    (irule identity_ghost_updates >> simp[]) >> simp[]
QED

Theorem dload_boundary_core_identity_index:
  MEM i.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\ i.inst_outputs = [] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==>
      (lookup_var v (s' with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t' with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    s'=s /\ t'=t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_boundary_core_identity >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> gvs[]
QED
