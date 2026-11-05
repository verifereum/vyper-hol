Theory lowerDloadPtrBranch
Ancestors
  lowerDloadPtrAggregate lowerDloadPtrRel lowerDloadPtrCall
  lowerDloadPtrScalar lowerDloadPtrPhi lowerDloadPtrStatic
  lowerDloadPtrBlockEntry lowerDloadPtrJointEntry lowerDloadDefs
  ptrDiscipline pointerConfinedDefs venomExecSemantics venomState venomInst
  memLocDefs finite_map list pred_set words contextCodegenRel

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

Theorem dload_boundary_core_branch_tracked:
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1 lbl. step_inst fuel Cs i s = OK s1 /\
    s1 = jump_to lbl s /\ t1 = jump_to lbl t /\
    s1.vs_current_bb = t1.vs_current_bb /\ s1.vs_prev_bb = t1.vs_prev_bb /\
    (s1.vs_halted <=> t1.vs_halted) /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH G H tn un s1 t1 cs ds
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_labels = t.vs_labels /\ s.vs_current_bb = t.vs_current_bb /\
   (s.vs_halted <=> t.vs_halted)` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `op_prov G op = NONE /\ op_taint tn op = {}` by
       (drule_all branch_operand_clean >> simp[]) >>
     `!v. op = Var v ==> v IN V` by (simp[] >> metis_tac[]) >>
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

Theorem lower_dload_function_supply_entry_ghosts:
  lower_dload_function_supply q f = (g,q') /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  enters_block g t t2 ==>
  entry_prov g t H = entry_prov f s H /\
  entry_taint_vars g t un = entry_taint_vars f s un
Proof
  simp[lower_dload_function_supply_def, enters_block_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all lower_dload_blocks_supply_lookup >> strip_tac >>
  drule lower_dload_block_supply_phi_exact >> strip_tac >>
  simp[entry_prov_def, entry_taint_vars_def] >>
  metis_tac[phi_prefix_computations]
QED

Theorem dload_actual_branch_block_tracked:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!a v lbl op w. MEM a (fn_insts f) /\ a.inst_opcode = PHI /\
    a.inst_outputs = [v] /\ v IN V /\
    resolve_phi lbl a.inst_operands = SOME op /\ op = Var w ==> w IN V) /\
  lower_dload_function_supply q f = (g,q') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\ ~t1.vs_halted /\
  enters_block g t1 t2 /\ active_inst g j t2 ==>
  ?s1 s2 i' emitted'.
    step_inst fuel C i s = OK s1 /\ ~s1.vs_halted /\
    enters_block f s1 s2 /\
    frame_reachable vs C cs PG (entry_prov f s1 G)
      (entry_taint_vars f s1 tn) f i' s2 /\
    dload_control_match q f g s2 t2 i' emitted' 0 /\ j = HD emitted' /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s2 = NONE <=> lookup_var v t2 = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (entry_prov f s1 G) (entry_prov g t1 H)
      (entry_taint_vars f s1 tn) (entry_taint_vars g t1 un) s2 t2 cs ds
Proof
  strip_tac >>
  `MEM i (fn_insts f) /\ active_inst f i s` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN V /\ v IN set (fn_ir_vars f)` by
    metis_tac[fn_ir_vars_operand] >>
  drule_all (Q.INST [`U` |-> `set (fn_ir_vars f)`] dload_boundary_core_branch_tracked) >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `s1.vs_labels = t1.vs_labels` by
    (drule_at (Pat `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s1 t1 _ _`)
       dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `!a v. MEM a (fn_insts f) /\ MEM (Var v) a.inst_operands ==>
    v IN set (fn_ir_vars f)` by metis_tac[fn_ir_vars_operand] >>
  drule_at (Pat `enters_block _ _ _`) lower_dload_function_supply_enters_boundary_tracked >>
  disch_then drule_all >> strip_tac >>
  drule_all dload_enters_block_control_match >> strip_tac >>
  `active_inst f i' s'` by
    (qpat_x_assum `dload_control_match _ _ _ s' _ _ _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  `is_terminator i.inst_opcode` by gvs[MEM, is_terminator_def] >>
  `frame_reachable vs C cs PG (entry_prov f s1 G)
     (entry_taint_vars f s1 tn) f i' s'` by
    (irule frame_reachable_block >> metis_tac[]) >>
  drule_all lower_dload_function_supply_entry_ghosts >> strip_tac >>
  qexistsl [`s1`,`s'`,`i'`,`emitted`] >> simp[] >>
  gvs[entry_prov_def, entry_taint_vars_def]
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
  strip_tac >> irule dload_boundary_core_branch_tracked >> simp[] >> metis_tac[]
QED

Theorem dload_actual_branch_block:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  MEM i.inst_opcode [JMP; JNZ; DJMP] /\
  fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\
  (!v. MEM (Var v) i.inst_operands ==> ~retpc_var f v) /\
  lower_dload_function_supply q f = (g,q') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\ ~t1.vs_halted /\
  enters_block g t1 t2 /\ active_inst g j t2 ==>
  ?s1 s2 i' emitted'.
    step_inst fuel C i s = OK s1 /\ ~s1.vs_halted /\
    enters_block f s1 s2 /\
    frame_reachable vs C cs PG (entry_prov f s1 G)
      (entry_taint_vars f s1 tn) f i' s2 /\
    dload_control_match q f g s2 t2 i' emitted' 0 /\ j = HD emitted' /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s2 = NONE <=> lookup_var v t2 = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (entry_prov f s1 G) (entry_prov g t1 H)
      (entry_taint_vars f s1 tn) (entry_taint_vars g t1 un) s2 t2 cs ds
Proof
  strip_tac >> irule dload_actual_branch_block_tracked >> simp[] >>
  metis_tac[retpc_phi_input_tracked, execEquivParamBaseTheory.resolve_phi_MEM, MEM]
QED

