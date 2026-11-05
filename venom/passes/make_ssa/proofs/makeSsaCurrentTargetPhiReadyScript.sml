Theory makeSsaCurrentTargetPhiReady
Ancestors makeSsaCurrentGraphDemand makeSsaCurrentMixedBatchReady
  makeSsaCurrentReinsertionOrder makeSsaCurrentReinsertionNames
  makeSsaCurrentRetainedNonclobber makeSsaCurrentSourcePhiReady
  makeSsaCurrentInsertionInputOrigin makeSsaCurrentDefs venomWf
  venomExecSemantics venomExecProps venomState venomInst list cfgHelpers
  makeSsaCurrentMixedBatchSingleton makeSsaCurrentInsertedValue
  makeSsaCurrentReinsertionSlots makeSsaCurrentRetainedRead
  makeSsaCurrentFinalSlots makeSsaCurrentAnalysis makeSsaCurrentStaticCuts
  makeSsaCurrentPhaseShape makeSsaCurrentCompletedBatch
  makeSsaCurrentSurvivorNoOutput makeSsaCurrentPhiBatch rich_list


Theorem current_graph_target_phi_member_ready:
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
  MEM phi (collect_phis out.bb_instructions) ==>
  IS_SOME (eval_one_phi target phi)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspec_then `hb.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  qabbrev_tac `phis = collect_phis hb.bb_instructions` >>
  qabbrev_tac `tail = DROP (LENGTH phis) hb.bb_instructions` >>
  `MEM p (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `?ev. MEM ev events /\ current_event_label ev = p` by
    (irule current_certificate_event_at >> metis_tac[]) >>
  `current_graph_admissible fn fn' (CurrentStaticCut p h 0 0)` by
    (simp[current_graph_admissible_def, current_graph_predecessor_def] >> metis_tac[]) >>
  `collect_phis out.bb_instructions =
    TAKE (phi_prefix_length out.bb_instructions) out.bb_instructions` by
    (qspec_then `out.bb_instructions` (map_every assume_tac o CONJUNCTS)
       current_collect_phi_split >>
     `phi_prefix_length out.bb_instructions = LENGTH (collect_phis out.bb_instructions)` by
       metis_tac[current_phi_prefix_maximal_length] >>
     metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]) >>
  `phi_prefix_length hb.bb_instructions = LENGTH phis` by
    metis_tac[current_phi_prefix_maximal_length] >>
  (drule_all current_certificate_leading_slot >> strip_tac
   >- suspend "inserted"
   >> suspend "original")
QED

Resume current_graph_target_phi_member_ready[inserted]:
  `!i. i < LENGTH (collect_phis hb.bb_instructions) ==>
    ~MEM v (inst_defs (EL i hb.bb_instructions))` by
    (`MEM n (FLAT (MAP (\j. j.inst_outputs) (collect_phis out.bb_instructions)))` by
       (simp[MEM_FLAT, MEM_MAP] >> metis_tac[MEM]) >>
     metis_tac[current_certificate_survivor_no_phi_output]) >>
  `?value. lookup_var v after = SOME value` by
    (irule current_actual_insertion_input_defined >> metis_tac[]) >>
  `resolve_phi p phi.inst_operands =
    SOME (Var (latest_current_name (current_event_exit_rs ev) v))` by
    (asm_rewrite_tac[] >> irule current_certificate_inserted_edge_resolve >> metis_tac[]) >>
  `current_graph_demand fn fn' H (CurrentStaticCut p h 0 0)
    (Var v) (Var (latest_current_name (current_event_exit_rs ev) v))` by
    (irule current_graph_demand_phi_seed >> metis_tac[]) >>
  `eval_operand (Var v) incoming =
    eval_operand (Var (latest_current_name (current_event_exit_rs ev) v)) target` by
    metis_tac[] >>
  `eval_operand (Var v) incoming = SOME value` by
    (pure_rewrite_tac[eval_operand_def, lookup_var_def] >>
     qpat_x_assum `lookup_var v after = SOME value` mp_tac >>
     pure_rewrite_tac[lookup_var_def] >> asm_rewrite_tac[]) >>
  `eval_operand (Var (latest_current_name (current_event_exit_rs ev) v)) target = SOME value` by
    metis_tac[] >>
  qpat_x_assum `phi.inst_operands = _` kall_tac >>
  simp[eval_one_phi_def]
QED

Resume current_graph_target_phi_member_ready[original]:
  `i < LENGTH hb.bb_instructions /\
    (EL i hb.bb_instructions).inst_opcode = PHI /\
    MEM (EL i hb.bb_instructions) (collect_phis hb.bb_instructions)` by
    (`EL i hb.bb_instructions = EL i phis` by
       (qpat_assum `hb.bb_instructions = _ ++ _` (fn th => once_rewrite_tac[th]) >>
        simp[EL_APPEND_EQN]) >>
     conj_tac >- (qpat_assum `hb.bb_instructions = _ ++ _`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
     asm_rewrite_tac[] >> fs[Abbr `phis`, EVERY_EL] >> metis_tac[EL_MEM]) >>
  `?v value. MEM (p,v) (phi_pairs (EL i hb.bb_instructions).inst_operands) /\
    resolve_phi p (EL i hb.bb_instructions).inst_operands = SOME (Var v) /\
    lookup_var v after = SOME value` by
    (irule current_actual_source_phi_selected >> metis_tac[]) >>
  `inst_wf (EL i hb.bb_instructions)` by
    (fs[fn_inst_wf_def] >> first_x_assum irule >> qexists `hb` >>
     conj_tac >- metis_tac[lookup_block_MEM] >> metis_tac[EL_MEM]) >>
  `phi_well_formed (EL i hb.bb_instructions).inst_operands` by
    (qpat_x_assum `inst_wf (EL i _)` (mp_tac o REWRITE_RULE [inst_wf_def]) >>
     asm_rewrite_tac[] >> simp[]) >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_certificate_event_labels_distinct] >>
  `MEM h (case ALOOKUP (current_succ_map fn) p of NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `resolve_phi p phi.inst_operands =
    SOME (Var (latest_current_name (current_event_exit_rs ev) v))` by
    (qpat_assum `phi.inst_operands = _` (fn th => once_rewrite_tac[th]) >>
     drule current_wf_phi_slots >> disch_then (fn th => once_rewrite_tac[th]) >>
     irule current_event_fold_selected_slot >> metis_tac[current_wf_phi_slots]) >>
  `current_graph_demand fn fn' H (CurrentStaticCut p h 0 0)
    (Var v) (Var (latest_current_name (current_event_exit_rs ev) v))` by
    (irule current_graph_demand_phi_seed >> metis_tac[]) >>
  `eval_operand (Var v) incoming =
    eval_operand (Var (latest_current_name (current_event_exit_rs ev) v)) target` by
    metis_tac[] >>
  `eval_operand (Var v) incoming = SOME value` by
    (pure_rewrite_tac[eval_operand_def, lookup_var_def] >>
     qpat_x_assum `lookup_var v after = SOME value` mp_tac >>
     pure_rewrite_tac[lookup_var_def] >> asm_rewrite_tac[]) >>
  `eval_operand (Var (latest_current_name (current_event_exit_rs ev) v)) target = SOME value` by
    metis_tac[] >>
  qpat_x_assum `phi.inst_operands = _` kall_tac >>
  simp[eval_one_phi_def]
QED

Finalise current_graph_target_phi_member_ready

Theorem current_graph_target_phi_batch_exists:
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
    eval_operand x incoming = eval_operand y target) ==>
  ?post. eval_phis target out.bb_instructions = OK post /\
    execution_frame post = execution_frame target
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY IS_SOME (MAP (eval_one_phi target) (collect_phis out.bb_instructions))` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule current_graph_target_phi_member_ready >> metis_tac[]) >>
  qspec_then `out.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  qexists `FOLDR (\(out,value) t. update_var out value t) target
    (MAP (THE o eval_one_phi target) (collect_phis out.bb_instructions))` >>
  conj_tac
  >- (drule current_eval_phis_batch >>
      disch_then (qspecl_then [`target`, `DROP (LENGTH (collect_phis out.bb_instructions)) out.bb_instructions`] mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >>
      qpat_assum `EVERY IS_SOME _` (fn th => rewrite_tac[th]) >>
      metis_tac[]) >>
  rewrite_tac[current_phi_writes_frame]
QED
