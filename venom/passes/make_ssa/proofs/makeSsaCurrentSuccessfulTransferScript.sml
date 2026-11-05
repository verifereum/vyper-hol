Theory makeSsaCurrentSuccessfulTransfer
Ancestors makeSsaCurrentGraphDemand makeSsaCurrentSubstitutionSound
  makeSsaCurrentTargetPhiReady makeSsaCurrentStaticCuts
  makeSsaCurrentStaticDemandProbe makeSsaCurrentCleanupRuntime
  venomExecSemantics venomWf list rich_list cfgHelpers
  makeSsaCurrentMixedBatchReady makeSsaCurrentCompletedBatch
  makeSsaCurrentPhaseShape makeSsaCurrentInsertedValue phiTransform

Theorem current_graph_successful_batch_transfer:
  current_graph_edge fn fn' (CurrentStaticCut p h 0 0) d 0 /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h fn'.fn_blocks = SOME out /\
  source.vs_prev_bb = SOME p /\ target.vs_prev_bb = SOME p /\
  EVERY inst_wf (TAKE (phi_prefix_length old.bb_instructions) old.bb_instructions) /\
  EVERY inst_wf (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions) /\
  eval_phis source old.bb_instructions = OK post /\
  eval_phis target out.bb_instructions = OK post' /\
  (!x y. current_graph_demand fn fn' H (CurrentStaticCut p h 0 0) x y ==>
    eval_operand x source = eval_operand y target) ==>
  !x y. current_graph_demand fn fn' H d x y ==>
    eval_operand x post = eval_operand y post'
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?u. current_static_phi_subst p
    (TAKE (phi_prefix_length old.bb_instructions) old.bb_instructions) x =
      SOME (CurrentStaticRead u) /\ eval_operand x post = eval_operand u source` by
    (irule current_static_phi_prefix_subst_sound >> metis_tac[]) >>
  `?v. current_static_phi_subst p
    (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions) y =
      SOME (CurrentStaticRead v) /\ eval_operand y post' = eval_operand v target` by
    (irule current_static_phi_prefix_subst_sound >> metis_tac[]) >>
  `current_graph_back fn fn' (CurrentStaticCut p h 0 0) 0 x y
     (CurrentStaticRead u) (CurrentStaticRead v)` by
    (simp[current_graph_back_def] >> metis_tac[current_graph_edge_endpoints]) >>
  `current_graph_demand fn fn' H (CurrentStaticCut p h 0 0) u v` by
    metis_tac[current_graph_demand_rules] >> metis_tac[]
QED

Theorem current_graph_successful_copy_transfer:
  current_graph_edge fn fn' (CurrentStaticCut p h i j) d 1 /\
  lookup_block h fn'.fn_blocks = SOME out /\
  current_cleanup_shape (EL j out.bb_instructions) /\
  step_inst_base (EL j out.bb_instructions) target = OK post /\
  (!x y. current_graph_demand fn fn' H (CurrentStaticCut p h i j) x y ==>
    eval_operand x source = eval_operand y target) ==>
  !x y. current_graph_demand fn fn' H d x y ==>
    eval_operand x source = eval_operand y post
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?v. current_static_copy_subst (EL j out.bb_instructions) y =
      SOME (CurrentStaticRead v) /\ eval_operand y post = eval_operand v target` by
    (irule current_static_copy_subst_sound >> metis_tac[]) >>
  `current_graph_back fn fn' (CurrentStaticCut p h i j) 1 x y
     (CurrentStaticRead x) (CurrentStaticRead v)` by
    (drule current_graph_edge_endpoints >> strip_tac >>
     simp[current_graph_back_def] >>
     qpat_x_assum `current_graph_admissible fn fn' (CurrentStaticCut p h i j)` mp_tac >>
     simp[current_graph_admissible_def] >> metis_tac[]) >>
  `current_graph_demand fn fn' H (CurrentStaticCut p h i j) x v` by
    metis_tac[current_graph_demand_rules] >> metis_tac[]
QED

Theorem current_graph_actual_phi_batch_transfer:
  current_structural_certificate s fn fn' s' A H events /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\ fn_phis_cover_preds fn /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ entry_block fn = SOME eb /\
  current_actual_domain_cut fn (CurrentBody fuel pb) before /\
  before.vs_current_bb = p /\ get_instruction pb before.vs_inst_idx = SOME inst /\
  inst_wf inst /\ is_terminator inst.inst_opcode /\ step_inst fuel ctx inst before = OK after /\
  lookup_block p fn.fn_blocks = SOME pb /\ lookup_block h fn.fn_blocks = SOME hb /\
  lookup_block h fn'.fn_blocks = SOME out /\ fn_cfg_edge fn p h /\
  incoming.vs_prev_bb = SOME p /\ incoming.vs_vars = after.vs_vars /\
  target.vs_prev_bb = SOME p /\
  (!x y. current_graph_demand fn fn' H (CurrentStaticCut p h 0 0) x y ==>
    eval_operand x incoming = eval_operand y target) /\
  eval_phis incoming hb.bb_instructions = OK source_post ==>
  ?target_post. eval_phis target out.bb_instructions = OK target_post /\
    execution_frame target_post = execution_frame target /\
    (!x y. current_graph_demand fn fn' H
      (CurrentStaticCut p h (phi_prefix_length hb.bb_instructions)
        (phi_prefix_length out.bb_instructions)) x y ==>
      eval_operand x source_post = eval_operand y target_post)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_graph_target_phi_batch_exists >> strip_tac >>
  `EVERY inst_wf (TAKE (phi_prefix_length hb.bb_instructions) hb.bb_instructions)` by
    (irule EVERY_TAKE >> fs[fn_inst_wf_def, EVERY_MEM] >>
     metis_tac[lookup_block_MEM]) >>
  qspec_then `hb.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  `EVERY inst_wf (collect_phis out.bb_instructions)` by
    (irule current_certificate_leading_phi_wf >> metis_tac[]) >>
  `EVERY inst_wf (TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions)` by
    (qspec_then `out.bb_instructions` (map_every assume_tac o CONJUNCTS)
      current_collect_phi_split >>
     `phi_prefix_length out.bb_instructions = LENGTH (collect_phis out.bb_instructions)` by
       metis_tac[current_phi_prefix_maximal_length] >>
     metis_tac[TAKE_LENGTH_APPEND]) >>
  qexists `post` >> conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  `current_graph_admissible fn fn' (CurrentStaticCut p h 0 0)` by
    (simp[current_graph_admissible_def, current_graph_predecessor_def] >> metis_tac[]) >>
  `current_graph_admissible fn fn'
    (CurrentStaticCut p h (phi_prefix_length hb.bb_instructions)
      (phi_prefix_length out.bb_instructions))` by
    metis_tac[current_graph_demand_admissible] >>
  `current_graph_edge fn fn' (CurrentStaticCut p h 0 0)
    (CurrentStaticCut p h (phi_prefix_length hb.bb_instructions)
      (phi_prefix_length out.bb_instructions)) 0` by
    (simp[current_graph_edge_def, current_static_edge_def] >> metis_tac[]) >>
  drule_all current_graph_successful_batch_transfer >>
  simp[]
QED
