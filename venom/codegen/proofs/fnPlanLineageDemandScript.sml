Theory fnPlanLineageDemand
Ancestors
  cfgCorrectnessProof
  fnPlanLineageDemandSupport livenessProofs livenessConvergenceProofs codegenReadyCompute cfgAnalysisProps venomWf stackPlanGen callLayoutDefs list rich_list

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

Definition projected_demand_wf_def:
  projected_demand_wf fn st <=>
    (!pb bb. MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
       fn_reachable fn pb.bb_label /\ fn_cfg_edge fn pb.bb_label bb.bb_label ==>
       EVERY (def_available_at fn pb NONE)
         (input_vars_from pb.bb_label bb.bb_instructions
           (df_at [] st bb.bb_label 0))) /\
    (!eb. entry_block fn = SOME eb ==> df_at [] st eb.bb_label 0 = [])
End

Theorem projected_demand_live_out:
  !fn st bb.
    wf_function fn /\ projected_demand_wf fn st /\
    MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label ==>
    EVERY (demand_available fn bb (LENGTH bb.bb_instructions))
      (liveness_out fn.fn_blocks (cfg_analyze fn) bb.bb_label st)
Proof
  rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all demand_available_endpoint >> disch_then (rewrite_tac o single) >>
  qpat_x_assum `MEM v _` mp_tac >>
  simp[livenessBlockProofsTheory.liveness_out_def,
       livenessTransferProofsTheory.mem_foldl_list_union, MEM_MAP] >>
  strip_tac >>
  `MEM s (bb_succs bb)` by metis_tac[cfg_analyze_preserves_bb_succs] >>
  `MEM s (fn_labels fn)` by metis_tac[wf_function_def, fn_succs_closed_def] >>
  gvs[venomInstTheory.fn_labels_def, MEM_MAP] >>
  rename1 `MEM succ_bb fn.fn_blocks` >>
  `lookup_block succ_bb.bb_label fn.fn_blocks = SOME succ_bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  gvs[livenessDefsTheory.liveness_edge_transfer_def] >>
  gvs[projected_demand_wf_def, EVERY_MEM] >>
  first_x_assum irule >> simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem projected_demand_init:
  !fn labels. projected_demand_wf fn (init_df_state [] labels)
Proof
  simp[projected_demand_wf_def, dfAnalyzeDefsTheory.init_df_state_def,
       dfAnalyzeDefsTheory.df_at_def,
       livenessDefsTheory.input_vars_from_def] >>
  rpt strip_tac >> Cases_on `NULL (collect_phis bb.bb_instructions)` >> simp[]
QED

Theorem projected_demand_block:
  !fn st lbl.
    codegen_ready_fn fn /\ projected_demand_wf fn st ==>
    projected_demand_wf fn
      (liveness_block fn.fn_blocks (cfg_analyze fn) lbl st)
Proof
  rpt strip_tac >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  simp[projected_demand_wf_def] >> conj_tac
  >- (rpt strip_tac >> Cases_on `bb.bb_label = lbl`
      >- (gvs[] >> simp[EVERY_MEM] >> rpt strip_tac >>
          irule liveness_block_projected_demand >>
          simp[] >> qexistsl_tac [`bb`, `cfg_analyze fn`, `st`] >> simp[] >>
          irule projected_demand_live_out >> simp[] >>
          metis_tac[venomExecProofsTheory.fn_reachable_step]) >>
      simp[livenessBlockProofsTheory.liveness_block_other_inst] >>
      gvs[projected_demand_wf_def] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `eb.bb_label = lbl`
  >- (gvs[] >>
      `MEM eb fn.fn_blocks /\ fn_reachable fn eb.bb_label` by
        (Cases_on `fn.fn_blocks` >>
         gvs[venomInstTheory.entry_block_def, fn_reachable_def,
             venomInstTheory.fn_entry_label_def]) >>
      `collect_phis eb.bb_instructions = []` by
        (gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]) >>
      `EVERY (demand_available fn eb (LENGTH eb.bb_instructions))
        (liveness_out fn.fn_blocks (cfg_analyze fn) eb.bb_label st)` by
        (irule projected_demand_live_out >> simp[]) >>
      Cases_on `df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn)
        eb.bb_label st) eb.bb_label 0 = []` >> simp[] >>
      `?v. MEM v (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn)
        eb.bb_label st) eb.bb_label 0)` by
        (Cases_on `df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn)
           eb.bb_label st) eb.bb_label 0` >> gvs[] >>
         qexists_tac `h` >> simp[]) >>
      drule_all liveness_block_entry_demand >>
      simp[raw_phi_inputs_def] >> strip_tac >>
      metis_tac[demand_available_entry]) >>
  simp[livenessBlockProofsTheory.liveness_block_other_inst] >>
  gvs[projected_demand_wf_def]
QED

Theorem projected_demand_fuel:
  codegen_ready_fn fn ==>
  !fuel wl st. projected_demand_wf fn st ==>
    projected_demand_wf fn
      (SND (wl_iterate_fuel fuel (liveness_changed fn.fn_blocks)
        (liveness_block fn.fn_blocks (cfg_analyze fn))
        (cfg_preds_of (cfg_analyze fn)) wl st))
Proof
  strip_tac >> Induct >> simp[worklistDefsTheory.wl_iterate_fuel_def] >>
  rpt strip_tac >> Cases_on `wl` >>
  simp[worklistDefsTheory.wl_iterate_fuel_def] >>
  Cases_on `liveness_changed fn.fn_blocks h st
    (liveness_block fn.fn_blocks (cfg_analyze fn) h st)` >>
  simp[worklistDefsTheory.wl_step_def, projected_demand_block]
QED

Theorem projected_demand_recompute:
  !fn. codegen_ready_fn fn ==> projected_demand_wf fn (liveness_recompute fn)
Proof
  rpt strip_tac >>
  `?fuel. liveness_recompute_fuel fuel fn = liveness_recompute fn` by
    metis_tac[livenessTerminationProofsTheory.liveness_recompute_fuel_agreement] >>
  `projected_demand_wf fn (liveness_recompute_fuel fuel fn)` by
    (simp_tac pure_ss [livenessDefsTheory.liveness_recompute_fuel_def, LET_THM] >>
     irule projected_demand_fuel >> simp[projected_demand_init]) >>
  gvs[]
QED

Theorem analyzed_entry_live_empty:
  !fn eb. codegen_ready_fn fn /\ entry_block fn = SOME eb ==>
    live_vars_at (liveness_analyze fn) eb.bb_label 0 = []
Proof
  rpt strip_tac >> drule projected_demand_recompute >>
  simp[projected_demand_wf_def, livenessDefsTheory.liveness_analyze_def,
       livenessDefsTheory.live_vars_at_def] >> metis_tac[]
QED

Theorem analyzed_hd_live_empty:
  !fn. codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label 0 = []
Proof
  rpt strip_tac >> irule analyzed_entry_live_empty >> simp[] >>
  Cases_on `fn.fn_blocks` >> gvs[venomInstTheory.entry_block_def]
QED

Theorem post_parameter_demand_ready:
  !fn. codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    EVERY (\v. MEM v (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions)))
      (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))
Proof
  rpt strip_tac >> irule post_parameter_demand >>
  simp[analyzed_hd_live_empty]
QED

Theorem projected_demand_ordinary_suffix:
  !fn st bb i.
    wf_function fn /\ def_dominates_uses fn /\ projected_demand_wf fn st /\
    MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i <= LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP i bb.bb_instructions) ==>
    EVERY (demand_available fn bb i)
      (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) bb.bb_label st) bb.bb_label i)
Proof
  rpt strip_tac >> irule liveness_block_ordinary_suffix_demand >> simp[] >>
  conj_tac
  >- (irule venomExecProofsTheory.MEM_lookup_block >>
      gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  irule projected_demand_live_out >> simp[]
QED

Theorem analyzed_endpoint_demand:
  !fn bb.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    fn_reachable fn bb.bb_label ==>
    EVERY (demand_available fn bb (LENGTH bb.bb_instructions))
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `liveness_instrs fn.fn_blocks bb.bb_label = bb.bb_instructions` by
    simp[livenessBlockProofsTheory.liveness_instrs_def] >>
  drule_all liveness_recompute_convergence >>
  simp[livenessDefsTheory.same_vars_set] >> strip_tac >>
  `EVERY (demand_available fn bb (LENGTH bb.bb_instructions))
    (liveness_out fn.fn_blocks (cfg_analyze fn) bb.bb_label (liveness_recompute fn))` by
    (irule projected_demand_live_out >> simp[projected_demand_recompute]) >>
  gvs[livenessDefsTheory.live_vars_at_def, livenessDefsTheory.liveness_analyze_def,
      EVERY_MEM, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem analyzed_ordinary_suffix_demand:
  !fn bb i.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    fn_reachable fn bb.bb_label /\
    i <= LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP i bb.bb_instructions) ==>
    EVERY (demand_available fn bb i)
      (live_vars_at (liveness_analyze fn) bb.bb_label i)
Proof
  rpt gen_tac >> measureInduct_on `LENGTH bb.bb_instructions - i` >> rpt strip_tac >>
  Cases_on `i = LENGTH bb.bb_instructions`
  >- (gvs[] >> irule analyzed_endpoint_demand >> simp[]) >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label i =
    liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >> simp[]) >>
  `(EL i bb.bb_instructions).inst_opcode <> PHI /\
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP (SUC i) bb.bb_instructions)` by
    (Cases_on `DROP i bb.bb_instructions` >- gvs[] >>
     drule DROP_CONS_EL >> strip_tac >> gvs[]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  rename1 `demand_available fn bb i v` >>
  Cases_on `MEM v (inst_uses (EL i bb.bb_instructions))`
  >- (`MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
      qpat_x_assum `def_dominates_uses fn` mp_tac >>
      simp[def_dominates_uses_def] >>
      disch_then (drule_then drule) >> simp[] >> strip_tac >>
      irule demand_available_before_use >> simp[] >>
      first_x_assum irule >> gvs[venomInstTheory.inst_uses_def] >>
      metis_tac[passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  gvs[livenessDefsTheory.liveness_transfer_def, livenessTransferProofsTheory.live_update_mem,
      venomInstTheory.inst_defs_def] >>
  `EVERY (demand_available fn bb (SUC i))
     (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (first_x_assum irule >> simp[] >> decide_tac) >>
  `demand_available fn bb (SUC i) v` by metis_tac[EVERY_MEM] >>
  metis_tac[demand_available_step_back]
QED
