Theory o1OpcodePassPreservation
Ancestors
  venomPassDispatcher venomPassSchedule venomInst list
  o1DretOpcodePreservation o1ConcretizeOpcodePreservation
  o1FmpOpcodePreservation o1DloadOpcodePreservation
  o1SimpleStructuralOpcodes
  o1DftOpcodePreservation o1CfgOpcodePreservation

Theorem execute_o1_fn_pass_no_returndatacopy:
  MEM pass o1_fn_passes /\
  execute_configured_fn_pass rp pass u s f = SOME out /\
  (!i. MEM i (fn_insts f) ==> i.inst_opcode <> RETURNDATACOPY) ==>
  !i. MEM i (fn_insts out.fpo_function) ==> i.inst_opcode <> RETURNDATACOPY
Proof
  simp[o1_fn_passes_def] >> strip_tac >>
  gvs[execute_configured_fn_pass_def, AllCaseEqs()]
  >- (metis_tac[make_ssa_current_fn_no_returndatacopy])
  >- (fs[GSYM EVERY_MEM] >> drule_all lower_dload_function_supply_no_returndatacopy >> simp[])
  >- (fs[GSYM EVERY_MEM] >> drule_all concretize_function_fuel_in_context_no_returndatacopy >> simp[])
  >- (fs[GSYM EVERY_MEM] >> drule_all fmp_lower_function_no_returndatacopy >> simp[])
  >- (metis_tac[make_ssa_current_fn_no_returndatacopy])
  >- (mp_tac (Q.INST [`op` |-> `RETURNDATACOPY`, `fn` |-> `f`]
        simplify_cfg_fn_with_labels_opcode_absence) >> simp[])
  >- (metis_tac[sue_expand_function_supply_no_returndatacopy])
  >- (metis_tac[dft_fn_no_returndatacopy]) >>
  mp_tac (Q.INST [`fn` |-> `f`, `s` |-> `s`]
    cfg_norm_function_supply_no_returndatacopy) >> simp[]
QED

Theorem execute_o1_pre_walk_opcode_absence:
  (op = RETURNDATACOPY \/ op = INVOKE) /\
  (pass = CFP_Simple VP_SimplifyCFG \/ pass = CFP_Simple VP_DretDesugar) /\
  execute_configured_fn_pass rp pass u s f = SOME out /\
  (!i. MEM i (fn_insts f) ==> i.inst_opcode <> op) ==>
  !i. MEM i (fn_insts out.fpo_function) ==> i.inst_opcode <> op
Proof
  strip_tac >> gvs[execute_configured_fn_pass_def, AllCaseEqs()]
  >- (mp_tac (Q.INST [`op` |-> `RETURNDATACOPY`, `fn` |-> `f`]
        simplify_cfg_fn_with_labels_opcode_absence) >> simp[])
  >- (fs[GSYM EVERY_MEM] >> metis_tac[dret_desugar_function_opcode_absence])
  >- (mp_tac (Q.INST [`op` |-> `INVOKE`, `fn` |-> `f`]
        simplify_cfg_fn_with_labels_opcode_absence) >> simp[]) >>
  fs[GSYM EVERY_MEM] >> metis_tac[dret_desugar_function_opcode_absence]
QED
