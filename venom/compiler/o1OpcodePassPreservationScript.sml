Theory o1OpcodePassPreservation
Ancestors
  venomPassDispatcher venomPassSchedule venomInst list
  o1DretOpcodePreservation o1ConcretizeOpcodePreservation
  o1FmpOpcodePreservation o1DloadOpcodePreservation
  o1SimpleStructuralOpcodes
  o1DftOpcodePreservation o1CfgOpcodePreservation

Theorem execute_o1_fn_pass_opcode_absence:
  (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\
  MEM pass o1_fn_passes /\
  execute_configured_fn_pass rp pass u s f = SOME out /\
  (!i. MEM i (fn_insts f) ==> i.inst_opcode <> op) ==>
  !i. MEM i (fn_insts out.fpo_function) ==> i.inst_opcode <> op
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `MEM _ _` (strip_assume_tac o SRULE [o1_fn_passes_def]) >>
  (* keep the opcode disjunction whole: gvs would split it *)
  qpat_x_assum `op = _ \/ _` mp_tac >>
  gvs[execute_configured_fn_pass_def, AllCaseEqs()] >> disch_tac
  >- (metis_tac[make_ssa_current_fn_opcode_absence])
  >- (qpat_x_assum `!i. _` (assume_tac o SRULE [GSYM EVERY_MEM]) >>
      simp[GSYM EVERY_MEM] >> drule_all lower_dload_function_supply_opcode_absence >> simp[])
  >- (qpat_x_assum `!i. _` (assume_tac o SRULE [GSYM EVERY_MEM]) >>
      simp[GSYM EVERY_MEM] >> drule_all concretize_function_fuel_in_context_opcode_absence >> simp[])
  >- (qpat_x_assum `!i. _` (assume_tac o SRULE [GSYM EVERY_MEM]) >>
      simp[GSYM EVERY_MEM] >> drule_all fmp_lower_function_opcode_absence >> simp[])
  >- (metis_tac[make_ssa_current_fn_opcode_absence])
  >- metis_tac[simplify_cfg_fn_with_labels_opcode_absence, pairTheory.FST]
  >- (metis_tac[sue_expand_function_supply_opcode_absence])
  >- (metis_tac[dft_fn_opcode_absence]) >>
  metis_tac[cfg_norm_function_supply_opcode_absence, pairTheory.FST]
QED

Theorem execute_o1_pre_walk_opcode_absence:
  (op = RETURNDATACOPY \/ op = INVOKE \/ op = CREATE \/ op = CREATE2) /\
  (pass = CFP_Simple VP_SimplifyCFG \/ pass = CFP_Simple VP_DretDesugar) /\
  execute_configured_fn_pass rp pass u s f = SOME out /\
  (!i. MEM i (fn_insts f) ==> i.inst_opcode <> op) ==>
  !i. MEM i (fn_insts out.fpo_function) ==> i.inst_opcode <> op
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `op = _ \/ _` mp_tac >>
  gvs[execute_configured_fn_pass_def, AllCaseEqs()] >> disch_tac
  >- metis_tac[simplify_cfg_fn_with_labels_opcode_absence, pairTheory.FST] >>
  qpat_x_assum `!i. _` (assume_tac o SRULE [GSYM EVERY_MEM]) >>
  simp[GSYM EVERY_MEM] >> metis_tac[dret_desugar_function_opcode_absence]
QED
