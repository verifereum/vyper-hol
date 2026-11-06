Theory ctorDeployLoweringFrameCallFree
Ancestors dretDesugarDefs venomInst asmIR stackPlanGen planExec stackPlanOps

Theorem expand_dret_pairs_call_free:
  !s cursor pairs body dsts final_cursor s'.
    expand_dret_pairs s cursor pairs =
      SOME (DretPairExpansion body dsts final_cursor s') ==>
    EVERY (\i. ~MEM i.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) body
Proof
  recInduct expand_dret_pairs_ind >>
  simp[expand_dret_pairs_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[mk_inst_def]
QED

Theorem replace_dret_inst_call_free:
  replace_dret_inst s cursor inst = SOME (replacement,s') ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) replacement
Proof
  simp[replace_dret_inst_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[mk_inst_def] >>
  drule expand_dret_pairs_call_free >> simp[]
QED

Theorem dret_desugar_insts_call_free:
  !insts s cursor result s'.
  dret_desugar_insts s cursor insts = SOME (result,s') /\
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) insts ==>
  EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) result
Proof
  Induct >> simp[dret_desugar_insts_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule replace_dret_inst_call_free >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem dret_desugar_blocks_call_free:
  !bbs s cursor result s'.
  dret_desugar_blocks s cursor bbs = SOME (result,s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) result
Proof
  Induct >> simp[dret_desugar_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule dret_desugar_insts_call_free >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem insert_after_last_param_every:
  !insts. P new /\ EVERY P insts ==>
    EVERY P (insert_after_last_param new insts)
Proof
  Induct >> simp[insert_after_last_param_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem dret_desugar_function_call_free:
  dret_desugar_function target s fn = SOME (fn',s') /\
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY (\i. ~MEM i.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn'.fn_blocks
Proof
  simp[dret_desugar_function_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule dret_desugar_blocks_call_free >> simp[] >> strip_tac >>
  irule insert_after_last_param_every >> simp[mk_inst_def]
QED

Theorem venom_to_evm_name_call_free:
  venom_to_evm_name op = SOME name /\
  ~MEM op [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]
Proof
  Cases_on `op` >> simp[venom_to_evm_name_def] >> rpt strip_tac >> gvs[]
QED

Theorem generate_emit_ops_call_free:
  generate_emit_ops inst log_topic_count ps = (ops, ps') /\
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  simp[generate_emit_ops_def, bump_emit_ops_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `fresh_label "return_label" ps` >> gvs[])
  >- (Cases_on `fresh_label "reachable" ps` >> gvs[]) >>
  drule venom_to_evm_name_call_free >> simp[]
QED

Theorem swap_name_prefix:
  TAKE 2 (swap_name n) = "SW"
Proof
  pure_rewrite_tac[swap_name_def] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >> simp[NoAsms]
QED

Theorem dup_name_prefix:
  TAKE 2 (dup_name n) = "DU"
Proof
  pure_rewrite_tac[dup_name_def] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >- simp[NoAsms] >>
  IF_CASES_TAC >> simp[NoAsms]
QED

Theorem swap_name_call_free:
  ~MEM (swap_name n) ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]
Proof
  mp_tac swap_name_prefix >>
  simp[] >> rpt strip_tac >> spose_not_then assume_tac >> gvs[]
QED

Theorem dup_name_call_free:
  ~MEM (dup_name n) ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]
Proof
  mp_tac dup_name_prefix >>
  simp[] >> rpt strip_tac >> spose_not_then assume_tac >> gvs[]
QED

Theorem exec_stack_op_call_free:
  (!name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (exec_stack_op initial_fmp sop)
Proof
  Cases_on `sop` >> simp[exec_stack_op_def]
  >- (Cases_on `o'` >> simp[exec_stack_op_def])
  >- (mp_tac swap_name_call_free >> simp[]) >>
  mp_tac dup_name_call_free >> simp[]
QED

Theorem execute_plan_call_free:
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (execute_plan initial_fmp ops)
Proof
  Induct_on `ops` >> simp[execute_plan_def] >> rpt strip_tac
  >- (irule (SRULE [] exec_stack_op_call_free) >> simp[]) >>
  fs[execute_plan_def]
QED

Theorem generate_emit_ops_assembly_call_free:
  generate_emit_ops inst log_topic_count ps = (ops,ps') /\
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (execute_plan initial_fmp ops)
Proof
  strip_tac >> irule execute_plan_call_free >>
  drule_all generate_emit_ops_call_free >> simp[]
QED

Theorem do_spill_tos_no_emit:
  !ps ops ps'. do_spill_tos ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  rpt gen_tac >> Cases_on `alloc_spill_slot ps.ps_alloc` >>
  simp[do_spill_tos_def] >> rpt strip_tac >> gvs[]
QED

Theorem do_spill_at_no_emit:
  do_spill_at dist ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  Cases_on `dist = 0`
  >- (simp[do_spill_at_def] >> metis_tac[do_spill_tos_no_emit]) >>
  Cases_on `do_spill_tos (ps with ps_stack := stack_swap dist ps.ps_stack)` >>
  simp[do_spill_at_def] >> rpt strip_tac >> gvs[] >>
  drule do_spill_tos_no_emit >> simp[]
QED

Theorem do_restore_no_emit:
  do_restore op ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[do_restore_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem restore_spilled_plan_no_emit:
  !operands ps ops ps'. restore_spilled_plan operands ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  Induct >- simp[restore_spilled_plan_def] >>
  rpt gen_tac >>
  Cases_on `do_restore h ps` >>
  rename1 `do_restore h ps = (ops1,ps1)` >>
  Cases_on `restore_spilled_plan operands ps1` >>
  simp[restore_spilled_plan_def] >> rpt strip_tac >> gvs[] >>
  drule do_restore_no_emit >> simp[] >> metis_tac[]
QED

Theorem spill_fold_no_emit[local]:
  !(items:operand list) ops offs al spill_ops offsets alloc'.
    FOLDL (\(ops,offs,al) item.
      (\(off,al'). (ops ++ [SOSpill off], SNOC off offs, al'))
        (alloc_spill_slot al))
      (ops,offs,al) items = (spill_ops,offsets,alloc') ==>
    EVERY (\sop. !name. sop <> SOEmit name) ops ==>
    EVERY (\sop. !name. sop <> SOEmit name) spill_ops
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`ops ++ [SOSpill q]`, `SNOC q offs`, `r`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem do_swap_no_emit:
  do_swap dist ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[do_swap_def] >>
  Cases_on `dist = 0` >- simp[] >>
  Cases_on `dist <= 16` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >> pairarg_tac >> rpt strip_tac >> gvs[] >>
  drule spill_fold_no_emit >> simp[] >>
  strip_tac >> simp[listTheory.EVERY_MAP]
QED

Theorem do_dup_no_emit:
  do_dup dist ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[do_dup_def] >>
  Cases_on `dist <= 15` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  simp[] >> pairarg_tac >> rpt strip_tac >> gvs[] >>
  drule spill_fold_no_emit >> simp[] >> strip_tac >>
  simp[listTheory.EVERY_FLAT, listTheory.EVERY_MAP] >>
  Cases_on `dist - 15 <= 16` >> simp[]
QED

Theorem reduce_depth_plan_no_emit:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops,ps') ==>
    EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  Induct >- simp[reduce_depth_plan_def] >> rpt gen_tac >>
  simp[reduce_depth_plan_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule do_spill_at_no_emit >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem reorder_one_no_emit:
  reorder_one dfg target_ops target_idx op ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[reorder_one_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_restore_no_emit >>
  imp_res_tac reduce_depth_plan_no_emit >>
  imp_res_tac do_swap_no_emit >> simp[]
QED

Theorem reorder_fold_no_emit[local]:
  !items ops ps result ps'.
  FOLDL (\(ops,ps) (idx,op).
    (\(step_ops,ps'). (ops ++ step_ops,ps'))
      (reorder_one dfg target_ops idx op ps))
    (ops,ps) items = (result,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops ==>
  EVERY (\sop. !name. sop <> SOEmit name) result
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >>
  Cases_on `reorder_one dfg target_ops h0 h1 ps` >>
  simp[] >> rpt strip_tac >>
  drule reorder_one_no_emit >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem reorder_plan_no_emit:
  reorder_plan dfg target_ops ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[reorder_plan_def] >> strip_tac >>
  drule reorder_fold_no_emit >> simp[]
QED

Theorem popmany_fold_no_emit[local]:
  !items ops ps result ps'.
  FOLDL (\(ops,ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops,ps)
    | SOME dist =>
      (\(swap_ops,ps').
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack))
      (if dist = 0 then ([],ps) else do_swap dist ps))
    (ops,ps) items = (result,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops ==>
  EVERY (\sop. !name. sop <> SOEmit name) result
Proof
  Induct >- simp[] >> rpt gen_tac >>
  Cases_on `stack_get_depth h ps.ps_stack`
  >- (simp[] >> metis_tac[]) >>
  rename1 `stack_get_depth h ps.ps_stack = SOME dist` >>
  Cases_on `dist = 0`
  >- (simp[] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  Cases_on `do_swap dist ps` >> simp[] >> rpt strip_tac >>
  drule do_swap_no_emit >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem popmany_individual_no_emit:
  popmany_individual to_pop ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[popmany_individual_def] >> strip_tac >>
  drule popmany_fold_no_emit >> simp[]
QED

Theorem popmany_plan_no_emit:
  popmany_plan operands ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  Cases_on `operands` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (pairarg_tac >> gvs[] >> drule do_swap_no_emit >> simp[])
  >- (drule popmany_individual_no_emit >> simp[]) >>
  drule popmany_individual_no_emit >> simp[]
QED

Theorem no_emit_assembly_call_free:
  EVERY (\sop. !name. sop <> SOEmit name) ops ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (execute_plan initial_fmp ops)
Proof
  strip_tac >> irule execute_plan_call_free >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem emit_one_input_no_emit:
  emit_one_input opc next_liveness op ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  Cases_on `op` >> simp[emit_one_input_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_restore_no_emit >> imp_res_tac do_dup_no_emit >> simp[]
QED

Theorem emit_input_plan_no_emit:
  !operands opc next_liveness ps ops ps'.
  emit_input_plan opc operands next_liveness ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  Induct >- simp[emit_input_plan_def] >> rpt gen_tac >>
  simp[emit_input_plan_def] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  drule emit_one_input_no_emit >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem optimistic_swap_plan_no_emit:
  optimistic_swap_plan dfg inst next_liveness next_is_terminator ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[optimistic_swap_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> drule do_swap_no_emit >> simp[]
QED

Theorem generate_phi_plan_no_emit:
  generate_phi_plan inst next_liveness is_halting ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[generate_phi_plan_def] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac do_dup_no_emit >> imp_res_tac popmany_plan_no_emit >>
  gvs[AllCaseEqs()]
QED

Theorem generate_offset_plan_no_emit:
  generate_offset_plan inst ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[generate_offset_plan_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem no_emit_plan_call_free:
  EVERY (\sop. !name. sop <> SOEmit name) ops ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem generate_regular_inst_plan_call_free:
  generate_regular_inst_plan liveness dfg cfg fn inst next_liveness
    is_halting next_is_terminator cur_bb_label ps = (ops,ps') /\
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  simp[generate_regular_inst_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >>
  drule_all (SRULE [] generate_emit_ops_call_free) >> strip_tac >>
  qpat_x_assum `generate_emit_ops _ _ _ = _` kall_tac >>
  imp_res_tac emit_input_plan_no_emit >>
  qpat_x_assum `emit_input_plan _ _ _ _ = _` kall_tac >>
  imp_res_tac reorder_plan_no_emit >>
  rpt (qpat_x_assum `reorder_plan _ _ _ = _` kall_tac) >>
  `EVERY (\sop. !name. sop <> SOEmit name) join_ops` by
    (qpat_x_assum `_ = (join_ops,ps2)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     IF_CASES_TAC >> simp[] >>
     Cases_on `join_target_ops liveness fn cur_bb_label inst` >> simp[] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac restore_spilled_plan_no_emit >>
     imp_res_tac reorder_plan_no_emit >> simp[]) >>
  `EVERY (\sop. !name. sop <> SOEmit name) reorder_ops` by
    (qpat_x_assum `_ = (reorder_ops,ps4)` mp_tac >>
     rpt IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  `EVERY (\sop. !name. sop <> SOEmit name) pop_ops` by
    (qpat_x_assum `_ = (pop_ops,ps8)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     drule popmany_plan_no_emit >> simp[]) >>
  `EVERY (\sop. !name. sop <> SOEmit name) opt_ops` by
    (qpat_x_assum `_ = (opt_ops,ps9)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     drule optimistic_swap_plan_no_emit >> simp[]) >>
  imp_res_tac no_emit_plan_call_free >>
  qpat_x_assum `_ = (ops,ps')` mp_tac >>
  Cases_on `inst.inst_outputs = []` >> simp[] >> strip_tac >> gvs[]
QED

Theorem generate_inst_plan_call_free:
  generate_inst_plan liveness dfg cfg fn inst next_liveness
    is_halting next_is_terminator cur_bb_label ps = SOME (ops,ps') /\
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  simp[generate_inst_plan_def] >> rpt IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[]
  >- (drule generate_phi_plan_no_emit >>
      disch_then (mp_tac o MATCH_MP no_emit_plan_call_free) >> simp[])
  >- (drule generate_offset_plan_no_emit >>
      disch_then (mp_tac o MATCH_MP no_emit_plan_call_free) >> simp[]) >>
  irule (SRULE [] generate_regular_inst_plan_call_free) >>
  metis_tac[]
QED

Theorem generate_inst_plan_assembly_call_free:
  generate_inst_plan liveness dfg cfg fn inst next_liveness
    is_halting next_is_terminator cur_bb_label ps = SOME (ops,ps') /\
  ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (execute_plan initial_fmp ops)
Proof
  strip_tac >> irule execute_plan_call_free >>
  irule generate_inst_plan_call_free >> metis_tac[]
QED

Theorem prepare_params_plan_no_emit:
  prepare_params_plan liveness fn ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[prepare_params_plan_def] >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac popmany_plan_no_emit >>
  imp_res_tac optimistic_swap_plan_no_emit >> simp[]
QED

Theorem clean_stack_plan_no_emit:
  clean_stack_plan liveness cfg fn bb ps = (ops,ps') ==>
  EVERY (\sop. !name. sop <> SOEmit name) ops
Proof
  simp[clean_stack_plan_def] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  rename1 `_ :: tail` >> Cases_on `tail` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule popmany_plan_no_emit >> simp[]
QED

Theorem generate_block_insts_plan_call_free:
  !insts i ps ops ps'.
  generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
    n_params block_len i insts ps = SOME (ops,ps') /\
  EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) insts ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  Induct >> simp[Once generate_block_insts_plan_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] generate_inst_plan_call_free) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem generate_block_plan_call_free:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops,ps') /\
  EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  simp[generate_block_plan_def] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >>
  `EVERY (\sop. !name. sop <> SOEmit name) param_ops` by
    (qpat_x_assum `_ = (param_ops,ps1)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     drule prepare_params_plan_no_emit >> simp[]) >>
  `EVERY (\sop. !name. sop <> SOEmit name) clean_ops` by
    (qpat_x_assum `_ = (clean_ops,ps2)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     drule clean_stack_plan_no_emit >> simp[]) >>
  qpat_x_assum `_ = (param_ops,ps1)` kall_tac >>
  qpat_x_assum `_ = (clean_ops,ps2)` kall_tac >>
  gvs[AllCaseEqs()] >>
  `EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) (non_param_insts bb)` by
    (gvs[non_param_insts_def, listTheory.EVERY_MEM, listTheory.MEM_FILTER]) >>
  drule_all generate_block_insts_plan_call_free >> strip_tac >>
  imp_res_tac no_emit_plan_call_free >> gvs[]
QED

Theorem generate_block_plan_assembly_call_free:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops,ps') /\
  EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (execute_plan initial_fmp ops)
Proof
  strip_tac >> irule execute_plan_call_free >>
  irule generate_block_plan_call_free >> metis_tac[]
QED

Theorem lookup_block_call_free[local]:
  !blocks lbl bb.
  EVERY (\b. EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) b.bb_instructions) blocks /\
  lookup_block lbl blocks = SOME bb ==>
  EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions
Proof
  rpt strip_tac >>
  `MEM bb blocks` by metis_tac[FIND_SOME_MEM, lookup_block_def] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem generate_plan_call_free:
  (!liveness dfg cfg fn worklist visited ps ops seen ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps = SOME (ops,seen,ps') /\
    EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
    EVERY (\sop. !name. sop = SOEmit name ==>
      ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops) /\
  (!liveness dfg cfg fn saved_stack saved_spilled succs visited ps ops seen ps'.
    generate_succs_plan liveness dfg cfg fn saved_stack saved_spilled succs visited ps = SOME (ops,seen,ps') /\
    EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
      [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
    EVERY (\sop. !name. sop = SOEmit name ==>
      ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `MEM lbl visited`
      >- gvs[Once generate_fn_plan_aux_def]
      >> Cases_on `lookup_block lbl fn.fn_blocks`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
      Cases_on `generate_block_plan liveness dfg cfg fn bb ps`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `generate_block_plan liveness dfg cfg fn bb ps = SOME bp` >>
      PairCases_on `bp` >>
      Cases_on `generate_succs_plan liveness dfg cfg fn bp1.ps_stack
                  bp1.ps_spilled (cfg_succs_of cfg lbl) (lbl::visited) bp1`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME sr` >>
      PairCases_on `sr` >>
      Cases_on `generate_fn_plan_aux liveness dfg cfg fn worklist sr1 sr2`
      >- gvs[Once generate_fn_plan_aux_def]
      >> rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME rr` >>
      PairCases_on `rr` >>
      gvs[Once generate_fn_plan_aux_def] >> rpt strip_tac >>
      drule_all (SRULE [] lookup_block_call_free) >> strip_tac >>
      drule_all (SRULE [] generate_block_plan_call_free) >> strip_tac >>
      gvs[])
  >- (rpt gen_tac >> simp[Once generate_fn_plan_aux_def])
  >> rpt gen_tac >> strip_tac >>
     Cases_on `generate_fn_plan_aux liveness dfg cfg fn [succ] visited
                 (ps with <| ps_stack := saved_stack;
                             ps_spilled := saved_spilled |>)`
     >- gvs[Once (cj 4 generate_fn_plan_aux_def)]
     >> rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME sr` >>
     PairCases_on `sr` >>
     Cases_on `generate_succs_plan liveness dfg cfg fn saved_stack
                 saved_spilled succs sr1
                 (ps with <| ps_alloc := sr2.ps_alloc with
                               sa_free_slots := ps.ps_alloc.sa_free_slots;
                             ps_label_counter := sr2.ps_label_counter |>)`
     >- gvs[Once (cj 4 generate_fn_plan_aux_def)]
     >> rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME rr` >>
     PairCases_on `rr` >>
     gvs[Once (cj 4 generate_fn_plan_aux_def)]
QED

Theorem generate_fn_plan_aux_call_free = CONJUNCT1 generate_plan_call_free
Theorem generate_succs_plan_call_free = CONJUNCT2 generate_plan_call_free

Theorem generate_fn_plan_analyzed_call_free:
  generate_fn_plan_analyzed liveness dfg cfg fn spill_base lbl_ctr = SOME (ops,ps') /\
  EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  simp[generate_fn_plan_analyzed_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] generate_fn_plan_aux_call_free) >> simp[]
QED

Theorem generate_fn_plan_call_free:
  generate_fn_plan fn spill_base lbl_ctr = SOME (ops,ps') /\
  EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  rewrite_tac[generate_fn_plan_def] >>
  MATCH_ACCEPT_TAC generate_fn_plan_analyzed_call_free
QED

Theorem generate_fn_plan_with_cleanup_analyzed_call_free:
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn spill_base lbl_ctr = SOME (ops,ps') /\
  EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  simp[generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE [] generate_fn_plan_aux_call_free) >> simp[]
QED

Theorem generate_fn_plan_with_cleanup_call_free:
  generate_fn_plan_with_cleanup ch growth fn spill_base lbl_ctr = SOME (ops,ps') /\
  EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\sop. !name. sop = SOEmit name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]) ops
Proof
  rewrite_tac[generate_fn_plan_with_cleanup_def] >>
  MATCH_ACCEPT_TAC generate_fn_plan_with_cleanup_analyzed_call_free
QED

Theorem generate_fn_plan_assembly_call_free:
  generate_fn_plan fn spill_base lbl_ctr = SOME (ops,ps') /\
  EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (execute_plan initial_fmp ops)
Proof
  strip_tac >> irule execute_plan_call_free >>
  irule generate_fn_plan_call_free >> metis_tac[]
QED

Theorem generate_fn_plan_with_cleanup_assembly_call_free:
  generate_fn_plan_with_cleanup ch growth fn spill_base lbl_ctr = SOME (ops,ps') /\
  EVERY (\bb. EVERY (\inst. ~MEM inst.inst_opcode
    [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\a. !name. a = AsmOp name ==>
    ~MEM name ["CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"])
    (execute_plan initial_fmp ops)
Proof
  strip_tac >> irule execute_plan_call_free >>
  irule generate_fn_plan_with_cleanup_call_free >> metis_tac[]
QED
