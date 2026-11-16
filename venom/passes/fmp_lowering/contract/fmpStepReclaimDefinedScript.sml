(*
 * A reclaim target is written on every path to its point.  Along any CFG
 * path from the entry, the accepted reclaim analysis has a state at every
 * point, and each mark on its stack is the output of an instruction
 * earlier on the path: the entry stack is empty, the transfer only pushes
 * a DALLOCA's output, and across an edge the successor's entry stack is a
 * prefix of the predecessor's exit stack, since every block of an accepted
 * analysis is stable.  A restore's base is a mark on the stack at its
 * point, so FmpLowering's restore reads a variable written on every path.
 *
 * TOP-LEVEL:
 *   analyze_fmp_reclaims_target_defined
 *)
Theory fmpStepReclaimDefined
Ancestors
  fmpLowerReclaimPlan fmpReclaimProps fmpReclaimDefs fmpStepStack
  dfAnalyzeDefs cfgAnalysisProps venomWfProps venomWf venomInst
  venomExecProps list rich_list

(* Along a block, every mark on the stack was already a mark at the block
   entry or is the output of an earlier instruction of the block. *)
Theorem fmp_reclaim_states_block_defined[local]:
  !P infos fn states env bb st0.
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ MEM bb fn.fn_blocks /\
  df_at NONE states bb.bb_label 0 = SOME st0 /\
  (!b. MEM b st0.frs_stack ==> P b) ==>
  !k. k <= LENGTH bb.bb_instructions ==>
    ?st. df_at NONE states bb.bb_label k = SOME st /\
      !b. MEM b st.frs_stack ==>
        P b \/ ?i. i < k /\ MEM b (EL i bb.bb_instructions).inst_outputs
Proof
  rpt gen_tac >> strip_tac >> Induct
  >- (strip_tac >> qexists `st0` >> simp[]) >>
  strip_tac >>
  `k <= LENGTH bb.bb_instructions /\ k < LENGTH bb.bb_instructions` by
    simp[] >>
  first_x_assum drule >> strip_tac >>
  drule_all fmp_reclaim_states_df_at_suc >> strip_tac >>
  qabbrev_tac `inst = EL k bb.bb_instructions` >>
  `fmp_stack_valid (\b. MEM b st.frs_stack \/ MEM b inst.inst_outputs)
     (fmp_transfer infos fn (liveness_analyze fn) env (bb.bb_label,k) inst
        (SOME st))` by
    (irule fmp_transfer_stack >> simp[fmp_stack_valid_def, EVERY_MEM] >>
     metis_tac[fmp_single_output_member]) >>
  `?st'. fmp_transfer infos fn (liveness_analyze fn) env (bb.bb_label,k) inst
     (SOME st) = SOME st'` by metis_tac[fmp_transfer_some] >>
  gvs[fmp_stack_valid_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac
  >- (first_x_assum drule >> strip_tac >> simp[] >>
      disj2_tac >> qexists `i` >> simp[]) >>
  disj2_tac >> qexists `k` >> simp[Abbr `inst`]
QED

Theorem fmp_reclaim_states_path_defined[local]:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  entry_block fn = SOME ebb /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) ==>
  !path. is_fn_path fn path /\ path <> [] /\ HD path = ebb.bb_label ==>
  !bb k. MEM bb fn.fn_blocks /\ LAST path = bb.bb_label /\
    k <= LENGTH bb.bb_instructions ==>
    ?st. df_at NONE states bb.bb_label k = SOME st /\
      !b. MEM b st.frs_stack ==>
        (?n def_bb def_inst. n < LENGTH path - 1 /\
           MEM def_bb fn.fn_blocks /\ def_bb.bb_label = EL n path /\
           MEM def_inst def_bb.bb_instructions /\
           MEM b def_inst.inst_outputs) \/
        (?i. i < k /\ MEM b (EL i bb.bb_instructions).inst_outputs)
Proof
  strip_tac >> ho_match_mp_tac SNOC_INDUCT >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `path = []`
  >- (gvs[] >>
      drule_all fmp_reclaim_states_df_at_entry >> strip_tac >>
      `?st0. fmp_joined (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state))
         (cfg_analyze fn) states ebb.bb_label = SOME st0` by
        metis_tac[fmp_joined_entry_some] >>
      drule fmp_joined_entry_empty >> strip_tac >>
      qspecl_then [`\b. F`, `infos`, `fn`, `states`, `env`, `bb`, `st0`]
        mp_tac fmp_reclaim_states_block_defined >>
      impl_tac >- gvs[] >>
      disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  `is_fn_path fn path /\ fn_cfg_edge fn (LAST path) x` by
    metis_tac[is_fn_path_init, is_fn_path_last_edge] >>
  `HD path = ebb.bb_label` by (Cases_on `path` >> gvs[SNOC]) >>
  gvs[LAST_SNOC] >>
  qpat_x_assum `fn_cfg_edge _ _ _` (strip_assume_tac o
    REWRITE_RULE [fn_cfg_edge_def]) >>
  rename1 `MEM pred_bb fn.fn_blocks` >>
  first_x_assum (qspecl_then [`pred_bb`, `LENGTH pred_bb.bb_instructions`]
    mp_tac) >> simp[] >> strip_tac >>
  rename1 `df_at NONE states _ _ = SOME exit_st` >>
  drule_all fmp_reclaim_states_stable >> strip_tac >>
  drule_all fmp_reclaim_states_df_at_exit >> strip_tac >>
  `MEM pred_bb.bb_label (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (irule (iffLR cfg_edge_symmetry_uncond) >>
     irule bb_succs_in_cfg_succs >> gvs[fn_labels_def]) >>
  `?entry_st. fmp_joined (SOME (ebb.bb_label,SOME fmp_empty_reclaim_state))
     (cfg_analyze fn) states bb.bb_label = SOME entry_st` by
    (irule fmp_joined_pred_some >> metis_tac[]) >>
  `?ks. exit_st.frs_stack = entry_st.frs_stack ++ ks` by
    (irule fmp_joined_pred_prefix >> metis_tac[]) >>
  `df_at NONE states bb.bb_label 0 = SOME entry_st` by
    metis_tac[fmp_reclaim_states_df_at_entry] >>
  qabbrev_tac `P = \b. ?n def_bb def_inst. n < LENGTH path /\
     MEM def_bb fn.fn_blocks /\ def_bb.bb_label = EL n (SNOC bb.bb_label path) /\
     MEM def_inst def_bb.bb_instructions /\ MEM b def_inst.inst_outputs` >>
  `!b. MEM b entry_st.frs_stack ==> P b` by
    (rpt strip_tac >> `MEM b exit_st.frs_stack` by simp[] >>
     first_x_assum drule >> strip_tac >> simp[Abbr `P`]
     >- (qexistsl [`n`, `def_bb`, `def_inst`] >> simp[EL_SNOC]) >>
     qexistsl [`PRE (LENGTH path)`, `pred_bb`,
               `EL i pred_bb.bb_instructions`] >>
     `PRE (LENGTH path) < LENGTH path` by (Cases_on `path` >> gvs[]) >>
     gvs[EL_SNOC, EL_MEM, LAST_EL]) >>
  qspecl_then [`P`, `infos`, `fn`, `states`, `env`, `bb`, `entry_st`]
    mp_tac fmp_reclaim_states_block_defined >>
  impl_tac >- gvs[] >>
  disch_then (qspec_then `k` mp_tac) >> simp[Abbr `P`]
QED

(* A restore's base is written on every path to the restored instruction. *)
Theorem analyze_fmp_reclaims_target_defined:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  FLOOKUP plan (bb.bb_label,j) = SOME target /\ MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) ==>
  j < LENGTH bb.bb_instructions /\
  def_on_all_paths fn bb (SOME (EL j bb.bb_instructions)) target
Proof
  strip_tac >> drule_all analyze_fmp_reclaims_target_checked >> strip_tac >>
  rename1 `lookup_block _ _ = SOME bb0` >>
  `bb0 = bb` by
    (qspecl_then [`bb.bb_label`, `fn.fn_blocks`, `bb`] mp_tac
       MEM_lookup_block >> gvs[]) >>
  gvs[] >>
  `MEM target st.frs_stack` by
    (drule_at (Pos last) fmp_reclaim_target_stack >>
     disch_then (qspec_then `\b. MEM b st.frs_stack` mp_tac) >>
     simp[fmp_stack_valid_def, EVERY_MEM]) >>
  `?ebb. entry_block fn = SOME ebb` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  mp_tac fmp_reclaim_states_path_defined >>
  impl_tac >- simp[] >> strip_tac >>
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  gvs[fn_entry_label_def] >>
  first_x_assum (drule_at (Pos (el 2))) >> simp[] >>
  disch_then (qspecl_then [`bb`, `j`] mp_tac) >> simp[] >>
  strip_tac >> first_x_assum drule >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >> qexists `i` >> simp[] >> qexists `j` >> simp[]
QED

