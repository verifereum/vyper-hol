Theory fnPlanLineageDemand
Ancestors
  fnPlanLineageDemandSupport livenessProofs cfgAnalysisProps venomWf stackPlanGen callLayoutDefs list rich_list

Theorem live_prefix_demand:
  !fn lbl bb n v.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    n <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) lbl n) ==>
    MEM v (live_vars_at (liveness_analyze fn) lbl 0) \/
    MEM v (FLAT (MAP inst_defs (TAKE n bb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM v (FLAT (MAP inst_defs (TAKE n bb.bb_instructions)))`
  >- simp[] >>
  disj1_tac >>
  drule live_vars_at_propagate_range >> simp[] >>
  disch_then irule >> simp[] >>
  qexists_tac `n` >> simp[] >>
  rpt strip_tac >>
  `MEM (EL k bb.bb_instructions) (TAKE n bb.bb_instructions)` by
    (simp[MEM_EL] >> qexists_tac `k` >> simp[EL_TAKE]) >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem get_params_canonical_prefix:
  !params k tail_insts.
    param_insts_from k params /\ no_param_insts tail_insts ==>
    get_params (params ++ tail_insts) = params
Proof
  Induct_on `params` >> simp[param_insts_from_def]
  >- (Cases >> simp[get_params_def, no_param_insts_def]) >>
  rpt strip_tac >> gvs[param_inst_at_def, get_params_def] >>
  first_x_assum irule >> simp[] >> qexists_tac `SUC k` >> simp[]
QED

Theorem param_insts_from_defs:
  !params k.
    param_insts_from k params ==>
    FLAT (MAP inst_defs params) = MAP (\inst. HD inst.inst_outputs) params
Proof
  Induct_on `params` >> simp[param_insts_from_def] >>
  rpt strip_tac >> gvs[param_inst_at_def, venomInstTheory.inst_defs_def] >>
  Cases_on `h.inst_outputs` >> gvs[LENGTH_EQ_NUM_compute] >>
  first_x_assum irule >> qexists_tac `SUC k` >> simp[]
QED

Theorem post_parameter_demand:
  !fn.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label 0 = [] ==>
    EVERY (\v. MEM v
      (MAP (\inst. HD inst.inst_outputs)
        (get_params (HD fn.fn_blocks).bb_instructions)))
      (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))
Proof
  rpt strip_tac >>
  `wf_function fn /\ canonical_param_prefix fn` by
    gvs[codegen_ready_fn_def] >>
  qpat_x_assum `canonical_param_prefix fn` mp_tac >>
  rewrite_tac[canonical_param_prefix_iff] >>
  disch_then (qx_choose_then `entry` (qx_choose_then `rest`
    (qx_choose_then `users` (qx_choose_then `fmp` (qx_choose_then `retpc`
      (qx_choose_then `tail_insts` (map_every assume_tac o CONJUNCTS))))))) >>
  gnvs[] >>
  `get_params entry.bb_instructions = users ++ fmp ++ retpc` by
    (gnvs[] >> rewrite_tac[APPEND_ASSOC] >>
     irule get_params_canonical_prefix >> simp[] >>
     qexists_tac `0` >> simp[APPEND_ASSOC]) >>
  `MEM entry.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (mp_tac (Q.SPECL [`fn`, `entry`] cfg_analyze_preorder_entry_first) >>
     simp[venomInstTheory.entry_block_def] >>
     Cases_on `(cfg_analyze fn).cfg_dfs_pre` >> simp[] >> metis_tac[]) >>
  `lookup_block entry.bb_label fn.fn_blocks = SOME entry` by
    simp[venomInstTheory.lookup_block_def, FIND_thm] >>
  `LENGTH (get_params entry.bb_instructions) <=
     LENGTH entry.bb_instructions` by simp[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule live_prefix_demand >>
  disch_then (qspecl_then [`entry.bb_label`, `entry`,
    `LENGTH (users ++ fmp ++ retpc)`, `v`] mp_tac) >>
  gnvs[] >>
  drule param_insts_from_defs >> disch_then assume_tac >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  qpat_x_assum `FLAT _ = _` mp_tac >>
  simp[MAP_APPEND, FLAT_APPEND] >> metis_tac[MEM_APPEND]
QED

Theorem phi_selected_def_available:
  !fn bb inst pred v.
    def_dominates_uses fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    MEM (pred,v) (phi_pairs inst.inst_operands) ==>
    ?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
      fn_cfg_edge fn pred bb.bb_label /\
      def_available_at fn pred_bb NONE v
Proof
  rpt strip_tac >>
  `phi_edge_uses_wf fn bb inst` by
    (gvs[def_dominates_uses_def] >> metis_tac[]) >>
  gvs[phi_edge_uses_wf_def] >> metis_tac[]
QED

Theorem input_vars_from_def_available:
  !fn bb pred base v.
    def_dominates_uses fn /\ MEM bb fn.fn_blocks /\
    MEM v (input_vars_from pred bb.bb_instructions base) ==>
    MEM v base \/
    ?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
      fn_cfg_edge fn pred bb.bb_label /\
      def_available_at fn pred_bb NONE v
Proof
  rpt strip_tac >>
  drule livenessTransferProofsTheory.input_vars_from_phi_correct_proof >>
  strip_tac >- simp[] >>
  disj2_tac >> irule phi_selected_def_available >>
  metis_tac[]
QED

Theorem liveness_block_projected_demand:
  !fn pb bb cfg st v.
    wf_function fn /\ def_dominates_uses fn /\
    MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
    fn_reachable fn pb.bb_label /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
    EVERY (demand_available fn bb (LENGTH bb.bb_instructions))
      (liveness_out fn.fn_blocks cfg bb.bb_label st) /\
    MEM v (input_vars_from pb.bb_label bb.bb_instructions
      (df_at [] (liveness_block fn.fn_blocks cfg bb.bb_label st) bb.bb_label 0)) ==>
    def_available_at fn pb NONE v
Proof
  rpt strip_tac >> drule input_vars_from_projected_membership >> strip_tac
  >- (drule_all liveness_block_entry_demand >> strip_tac >> gvs[] >>
      irule demand_available_predecessor >> metis_tac[]) >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  drule_all phi_selected_def_available >> strip_tac >>
  `pred_bb = pb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[]
QED
