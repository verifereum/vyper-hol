Theory fnBlockPlanStaticPromises
Ancestors
  fnPlanLineage fnBlockPlanStaticInventory fnBlockPlanStaticRetRegion
  stackPlanOps stackPlanGen stackPlanTypes list

Theorem promise_do_dup[local]:
  !d ps. (SND (do_dup d ps)).ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[do_dup_def, LET_THM] >> IF_CASES_TAC >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem promise_do_restore[local]:
  !op ps. (SND (do_restore op ps)).ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[do_restore_def] >> CASE_TAC >> simp[]
QED

Theorem promise_do_spill[local]:
  !d ps. (SND (do_spill_at d ps)).ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem promise_reduce_depth[local]:
  !fuel targets op f n ps.
  (SND (reduce_depth_plan fuel targets op f n ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >> CASE_TAC >> simp[] >>
  IF_CASES_TAC >> simp[] >> CASE_TAC >> simp[] >>
  pairarg_tac >>
  Cases_on `reduce_depth_plan fuel targets op f n ps'` >> gvs[] >>
  metis_tac[promise_do_spill, pairTheory.SND]
QED

Theorem promise_restore_spilled[local]:
  !items ps. (SND (restore_spilled_plan items ps)).ps_cleanup_promised =
    ps.ps_cleanup_promised
Proof
  Induct >> simp[restore_spilled_plan_def, LET_THM] >> rpt gen_tac >>
  pairarg_tac >> Cases_on `restore_spilled_plan items ps1` >> gvs[] >>
  metis_tac[promise_do_restore, pairTheory.SND]
QED

Theorem promise_reorder_one[local]:
  !dfg targets idx op ps.
  (SND (reorder_one dfg targets idx op ps)).ps_cleanup_promised =
    ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[reorder_one_def, LET_THM] >>
  pairarg_tac >>
  `ps1.ps_cleanup_promised = ps.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> metis_tac[promise_do_restore, pairTheory.SND]) >>
  simp[] >> qpat_x_assum `_ = (restore_ops,ps1)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps1.ps_stack` >> simp[] >> pairarg_tac >>
  `ps2.ps_cleanup_promised = ps1.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> metis_tac[promise_reduce_depth, pairTheory.SND]) >>
  simp[] >> qpat_x_assum `_ = (reduce_ops,ps2)` kall_tac >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) ps2.ps_stack` >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[inventory_do_swap_promised, pairTheory.SND]
QED

Theorem promise_reorder_fold[local]:
  !items ops ps.
  (SND (FOLDL (\(ops,ps) (idx,op).
    let (step_ops,qs) = reorder_one dfg targets idx op ps in
    (ops ++ step_ops,qs)) (ops,ps) items)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  Induct >> simp[LET_THM] >> rpt gen_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [LET_THM]) >>
  PairCases_on `h` >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[promise_reorder_one, pairTheory.SND]
QED

Theorem promise_reorder[local]:
  !dfg targets ps. (SND (reorder_plan dfg targets ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  simp[reorder_plan_def, LET_THM, SRULE [LET_THM] promise_reorder_fold]
QED

Theorem promise_emit_one_input[local]:
  !opc live op ps. (SND (emit_one_input opc live op ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[emit_one_input_def, LET_THM] >> pairarg_tac >>
  `ps1.ps_cleanup_promised = ps.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> metis_tac[promise_do_restore, pairTheory.SND]) >>
  simp[] >> Cases_on `op` >> simp[] >> rpt IF_CASES_TAC >> simp[] >>
  CASE_TAC >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[promise_do_dup, pairTheory.SND]
QED

Theorem promise_emit_input[local]:
  !items opc live ps. (SND (emit_input_plan opc items live ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  Induct >> simp[emit_input_plan_def, LET_THM] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[promise_emit_one_input, pairTheory.SND]
QED

Theorem promise_optimistic[local]:
  !dfg inst live term ps.
  (SND (optimistic_swap_plan dfg inst live term ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >> CASE_TAC >>
  simp[inventory_do_swap_promised]
QED

Theorem promise_phi[local]:
  !inst live halt ps.
  (SND (generate_phi_plan inst live halt ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[generate_phi_plan_def, LET_THM] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack` >> simp[] >>
  pairarg_tac >>
  `ps'.ps_cleanup_promised = ps.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
     metis_tac[promise_do_dup, pairTheory.SND]) >>
  simp[] >> IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[] >>
  metis_tac[inventory_popmany_promised, pairTheory.SND]
QED

Theorem promise_offset[local]:
  !inst ps. (SND (generate_offset_plan inst ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[generate_offset_plan_def, LET_THM] >>
  Cases_on `EL 1 inst.inst_operands` >> simp[]
QED

Theorem promise_emit_ops[local]:
  !inst topics ps. (SND (generate_emit_ops inst topics ps)).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >~ [`venom_to_evm_name _ = SOME _`]
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (gvs[] >> simp[generate_emit_ops_def] >> rpt (CASE_TAC >> gvs[])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[] >> simp[generate_emit_ops_def] >> rpt (CASE_TAC >> gvs[])) >>
  Cases_on `inst.inst_opcode = DJMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      Cases_on `HD inst.inst_operands` >> simp[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = RET`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (gvs[] >> simp[generate_emit_ops_def, fresh_label_def]) >>
  Cases_on `inst.inst_opcode = LOG`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >> simp[generate_emit_ops_def]
QED

Theorem promise_outputs[local]:
  !outputs ps.
  (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
    ps outputs).ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  Induct >> simp[]
QED

Theorem promise_release_fold[local]:
  !items ps.
  (FOLDL (\s (op,off). s with <|ps_spilled := s.ps_spilled \\ op;
    ps_alloc := free_spill_slot off s.ps_alloc|>) ps items).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[]
QED

Theorem promise_release[local]:
  !live ps. (release_dead_spills live ps).ps_cleanup_promised =
  ps.ps_cleanup_promised
Proof
  simp[release_dead_spills_def, LET_THM, promise_release_fold]
QED

Theorem promise_regular[local]:
  !lv dfg cfg fn inst live halt term lbl ps.
  (SND (generate_regular_inst_plan lv dfg cfg fn inst live halt term lbl ps)).
    ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[generate_regular_inst_plan_def, LET_THM] >>
  pairarg_tac >>
  `ps1.ps_cleanup_promised = ps.ps_cleanup_promised` by
    metis_tac[promise_emit_input, pairTheory.SND] >>
  simp[] >> qpat_x_assum `_ = (input_ops,ps1)` kall_tac >> pairarg_tac >>
  `ps2.ps_cleanup_promised = ps1.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> pairarg_tac >> gvs[] >>
     Cases_on `reorder_plan dfg target_ops ps1'` >> gvs[] >>
     metis_tac[promise_restore_spilled, promise_reorder, pairTheory.SND]) >>
  simp[] >> qpat_x_assum `_ = (join_ops,ps2)` kall_tac >> pairarg_tac >>
  `ps4.ps_cleanup_promised = ps2.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     metis_tac[promise_reorder, pairTheory.SND]) >>
  simp[] >> qpat_x_assum `_ = (reorder_ops,ps4)` kall_tac >> pairarg_tac >>
  `ps7.ps_cleanup_promised = ps4.ps_cleanup_promised` by
    metis_tac[promise_emit_ops, promise_outputs, pairTheory.SND,
              plan_state_accfupds, plan_state_accessors] >>
  simp[] >> qpat_x_assum `_ = (emit_ops,ps7)` kall_tac >>
  IF_CASES_TAC >> simp[promise_release] >>
  pairarg_tac >>
  `ps8.ps_cleanup_promised = ps7.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> metis_tac[inventory_popmany_promised, pairTheory.SND]) >>
  simp[] >> pairarg_tac >>
  `ps9.ps_cleanup_promised = ps8.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> metis_tac[promise_optimistic, pairTheory.SND]) >>
  simp[promise_release]
QED

Theorem generate_inst_plan_promised:
  generate_inst_plan lv dfg cfg fn inst live halt term lbl ps = SOME (ops,qs) ==>
  qs.ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  simp[generate_inst_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac >>
  metis_tac[promise_phi, promise_offset, promise_regular, pairTheory.SND]
QED

Theorem promise_param_fold[local]:
  !params ps.
  (FOLDL (\s inst. s with ps_stack :=
    stack_push (Var (HD inst.inst_outputs)) s.ps_stack) ps params).
    ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  Induct >> simp[]
QED

Theorem prepare_params_plan_promised:
  !lv fn ps. (SND (prepare_params_plan lv fn ps)).ps_cleanup_promised =
    ps.ps_cleanup_promised
Proof
  rpt gen_tac >> simp[prepare_params_plan_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >>
  `ps''.ps_cleanup_promised = ps.ps_cleanup_promised` by
    metis_tac[inventory_popmany_promised, promise_param_fold, pairTheory.SND] >>
  simp[] >> qpat_x_assum `_ = (pop_ops,ps'')` kall_tac >>
  pairarg_tac >> simp[] >> metis_tac[promise_optimistic, pairTheory.SND]
QED

Theorem generate_block_insts_plan_promised:
  !insts i ps ops qs.
  generate_block_insts_plan lv dfg cfg fn lbl halt np blen i insts ps =
    SOME (ops,qs) ==> qs.ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  Induct >> simp[generate_block_insts_plan_def, LET_THM] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  drule generate_inst_plan_promised >> simp[]
QED
