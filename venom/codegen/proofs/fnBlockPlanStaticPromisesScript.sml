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
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[]) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[]) >>
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

Theorem promise_cleanup_unsafe[local]:
  ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth cfg fn bb n) ==>
  ~(SND (clean_stack_plan lv cfg fn bb ps)).ps_cleanup_promised
Proof
  strip_tac >> simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  rename1 `cfg_preds_of cfg bb.bb_label = pred::rest` >>
  Cases_on `rest` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `lookup_block pred fn.fn_blocks` >>
  simp[inventory_popmany_promised]
QED

Theorem ret_cleanup_plan_unpromised:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  ~ps.ps_cleanup_promised /\ clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
  ~qs.ps_cleanup_promised
Proof
  strip_tac >> drule_all inventory_ret_cleanup_not_safe >>
  disch_then (qspec_then `ps` assume_tac) >>
  drule_all promise_cleanup_unsafe >>
  disch_then (qspec_then `lv` mp_tac) >> simp[]
QED

Theorem ret_block_plan_unpromised:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  ~ps.ps_cleanup_promised /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops,qs) ==>
  ~qs.ps_cleanup_promised
Proof
  strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, LET_THM] >> pairarg_tac >>
  `~ps1.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> metis_tac[prepare_params_plan_promised, pairTheory.SND]) >>
  simp[] >> qpat_x_assum `_ = (param_ops,ps1)` kall_tac >>
  pairarg_tac >>
  `~ps2.ps_cleanup_promised` by
    (gvs[AllCaseEqs()] >> metis_tac[ret_cleanup_plan_unpromised]) >>
  simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule generate_block_insts_plan_promised >> simp[]
QED

Theorem generate_succs_plan_promised_mutual[local]:
  (!lv dfg cfg fn wl visited ps.
    generate_fn_plan_aux lv dfg cfg fn wl visited ps =
    generate_fn_plan_aux lv dfg cfg fn wl visited ps) /\
  (!lv dfg cfg fn ss sp succs visited ps.
    !ops visited' qs.
    generate_succs_plan lv dfg cfg fn ss sp succs visited ps =
      SOME (ops,visited',qs) ==>
    qs.ps_cleanup_promised = ps.ps_cleanup_promised)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[Once generate_fn_plan_aux_def]
  >> rpt gen_tac >> strip_tac >>
  simp[Once generate_fn_plan_aux_def, LET_THM] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem generate_succs_plan_promised:
  generate_succs_plan lv dfg cfg fn ss sp succs visited ps =
    SOME (ops,visited',qs) ==>
  qs.ps_cleanup_promised = ps.ps_cleanup_promised
Proof
  metis_tac[generate_succs_plan_promised_mutual]
QED

Theorem ret_region_calls_unpromised:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET ==>
  (!wl visited ps.
    dfs_aux_call lv dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base ctr) wl visited ps ==>
    LENGTH wl <= 1 /\
    ((!l. MEM l wl ==> ~cfg_path cfg l target) \/ ~ps.ps_cleanup_promised)) /\
  (!ss sp succs visited ps.
    dfs_succs_call lv dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base ctr) ss sp succs visited ps ==>
    ((!l. MEM l succs ==> ~cfg_path cfg l target) \/ ~ps.ps_cleanup_promised))
Proof
  strip_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (simp[init_cleanup_plan_state_def, init_plan_state_def])
  >- (rpt strip_tac >> rename1 `LENGTH (head::tail) <= 1` >>
      Cases_on `tail` >> gvs[])
  >- (rpt strip_tac >> rename1 `LENGTH (head::tail) <= 1` >>
      Cases_on `tail` >> gvs[])
  >- suspend "succs"
  >- (rpt strip_tac >> rename1 `LENGTH (head::tail) <= 1` >>
      Cases_on `tail` >> gvs[])
  >- (rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume ret_region_calls_unpromised[succs]:
  rpt strip_tac >>
  (Cases_on `cfg_path cfg lbl target`
   >- (disj2_tac >> gvs[] >> irule ret_block_plan_unpromised >>
       goal_assum (drule_at Any) >> simp[] >> metis_tac[])) >>
  disj1_tac >> rpt strip_tac >>
  drule_all cfg_path_predecessor_closed >> simp[]
QED

Finalise ret_region_calls_unpromised

Theorem ret_region_dfs_block_unpromised:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base ctr) lbl ps /\
  cfg_path cfg lbl target ==>
  ~ps.ps_cleanup_promised
Proof
  strip_tac >> drule_all ret_region_calls_unpromised >>
  disch_then (mp_tac o cj 1) >> strip_tac >>
  gvs[dfs_block_state_def] >> first_x_assum drule >> simp[] >>
  metis_tac[]
QED
