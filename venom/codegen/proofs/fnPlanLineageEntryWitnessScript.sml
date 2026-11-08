Theory fnPlanLineageEntryWitness
Ancestors
  venomExecProofs venomWf list relation
  simplifyCfgPhiRepair removeUnusedSsaProofs
  livenessAnalysisProps codegenReadyCompute cfgAnalysisProps venomInst

Theorem is_fn_path_first_entry:
  !path lbl.
  is_fn_path fn path /\ MEM lbl path /\ HD path <> lbl ==>
  ?pre. is_fn_path fn pre /\ pre <> [] /\ HD pre = HD path /\
    ~MEM lbl pre /\ fn_cfg_edge fn (LAST pre) lbl
Proof
  Induct >- simp[] >> rpt gen_tac >>
  namedCases_on `path` ["", "next rest"]
  >- (strip_tac >> gvs[]) >>
  simp[is_fn_path_def] >> disch_tac >>
  Cases_on `next = lbl`
  >- (qexists_tac `[h]` >> gvs[is_fn_path_def]) >>
  gvs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `h::pre` >>
  Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem fn_reachable_first_entry_predecessor:
  fn_reachable fn lbl /\ fn_entry_label fn = SOME entry /\ lbl <> entry ==>
  ?p. fn_cfg_edge fn p lbl /\ fn_reachable fn p /\ ~fn_dominates fn lbl p
Proof
  simp[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM lbl path` by
    (Cases_on `path` >- gvs[] >> metis_tac[rich_listTheory.MEM_LAST]) >>
  `HD path <> lbl` by gvs[] >>
  drule_all is_fn_path_first_entry >> strip_tac >>
  qexists_tac `LAST pre` >> simp[] >>
  conj_tac
  >- (drule_all is_fn_path_rtc >> gvs[]) >>
  simp[fn_dominates_def] >> disj2_tac >>
  qexists_tac `pre` >> gvs[]
QED

Theorem def_available_non_dominating_no_kill:
  ssa_form fn /\ MEM bb fn.fn_blocks /\
  ~fn_dominates fn bb.bb_label pb.bb_label /\
  def_available_at fn pb use_pos v ==>
  EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  gvs[def_available_at_def] >>
  `ALL_DISTINCT (FLAT (MAP (\b. FLAT (MAP (\i. i.inst_outputs) b.bb_instructions))
     fn.fn_blocks))` by
    (gvs[ssa_form_def, venomInstTheory.fn_insts_def, fn_insts_blocks_flat,
         MAP_FLAT, rich_listTheory.FLAT_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
  drule distinct_projection_member_eq >>
  disch_then (qspecl_then [`bb`, `def_bb`, `v`] mp_tac) >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem reachable_use_no_kill_live_entry:
  wf_function fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ MEM v (inst_uses inst) /\
  EVERY (\i. ~MEM v i.inst_outputs) bb.bb_instructions ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (drule fn_reachable_cfg_analyze >>
     drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl j)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_uses >>
     disch_then (qspecl_then [`lbl`, `bb`, `j`, `v`] mp_tac) >>
     simp[]) >>
  drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
  disch_then (qspecl_then [`lbl`, `bb`, `0`, `j`, `v`] mp_tac) >>
  simp[] >>
  gvs[EVERY_EL, inst_defs_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem reachable_phi_live_entry_representative:
  wf_function fn /\ wf_ssa fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
  ?p v. MEM (p,v) (phi_pairs inst.inst_operands) /\
    MEM v (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  drule_all fn_reachable_first_entry_predecessor >> strip_tac >>
  `phi_edge_uses_wf fn bb inst` by
    (gvs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  qpat_x_assum `phi_edge_uses_wf _ _ _` mp_tac >>
  simp[phi_edge_uses_wf_def] >> strip_tac >>
  `?v. MEM (p,v) (phi_pairs inst.inst_operands)` by
    (qpat_assum `!pred. fn_cfg_edge _ _ _ <=> _`
       (qspec_then `p` mp_tac) >> simp[] >>
     disch_then (qx_choose_then `pair` strip_assume_tac) >>
     PairCases_on `pair` >> gvs[] >> metis_tac[]) >>
  qpat_assum `!pred v. MEM (pred,v) _ ==> _` drule >> strip_tac >>
  `EVERY (\i. ~MEM v i.inst_outputs) bb.bb_instructions` by
    (irule def_available_non_dominating_no_kill >>
     goal_assum (drule_at Any) >> gvs[wf_ssa_def]) >>
  qexistsl [`p`, `v`] >> simp[] >>
  irule reachable_use_no_kill_live_entry >>
  goal_assum (drule_at Any) >> simp[inst_uses_def] >>
  metis_tac[cfgNormSupplyProofsTheory.MEM_phi_pairs_SND_operand_vars]
QED
