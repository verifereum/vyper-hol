Theory o1LabelFlowMiddleLive
Ancestors
  makeSsaCurrentSelectedLive livenessSoundProofs livenessLocalProofs
  dftWf livenessTransferProofs livenessDefs makeSsaDefs venomInst venomWf
  list rich_list alist

Theorem cfg_exec_path_positive_step:
  !k ps. cfg_exec_path cfg ps /\ SUC k < LENGTH ps /\
    0 < SND (EL (SUC k) ps) ==>
    FST (EL (SUC k) ps) = FST (EL k ps) /\
    SND (EL (SUC k) ps) = SND (EL k ps) + 1
Proof
  Induct
  >- (Cases_on `ps` >> simp[] >> Cases_on `t` >> simp[] >>
      PairCases_on `h` >> PairCases_on `h'` >>
      simp[cfg_exec_path_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `ps` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `t` mp_tac) >>
  Cases_on `t` >> gvs[] >> PairCases_on `h` >> PairCases_on `h'` >>
  gvs[cfg_exec_path_def]
QED

Theorem adjacent_definition_path_exclusion:
  (!l i. var_used_at bbs l i x ==>
     0 < i /\ var_defined_at bbs l (i - 1) x) /\
  ~var_used_at bbs l i x /\ cfg_exec_path cfg ((l,i)::ps) ==>
  ~used_before_defined bbs x ((l,i)::ps)
Proof
  strip_tac >> disch_tac >>
  gvs[used_before_defined_def] >>
  Cases_on `k` >> gvs[] >>
  `0 < SND (EL (SUC n) ((l,i)::ps)) /\
   var_defined_at bbs (FST (EL (SUC n) ((l,i)::ps)))
     (SND (EL (SUC n) ((l,i)::ps)) - 1) x` by (simp[] >> metis_tac[]) >>
  `SUC n < LENGTH ((l,i)::ps)` by simp[] >>
  drule_all cfg_exec_path_positive_step >> strip_tac >>
  qpat_x_assum `!j. j < SUC n ==> _` (qspec_then `n` mp_tac) >>
  gvs[]
QED

Theorem distinct_adjacent_read_index:
  ALL_DISTINCT (MAP (\j. j.inst_id) xs) /\ i < LENGTH xs /\
  xs = pre ++ [d; EL i xs] ++ post ==>
  i = LENGTH pre + 1
Proof
  strip_tac >>
  qspecl_then [`MAP (\j. j.inst_id) xs`,
    `MAP (\j. j.inst_id) (pre ++ [d])`,
    `MAP (\j. j.inst_id) post`, `i`] mp_tac ALL_DISTINCT_EL_APPEND >>
  simp[EL_MAP] >>
  impl_tac >- metis_tac[MAP_APPEND, MAP, APPEND_ASSOC, APPEND] >>
  simp[]
QED

Theorem collect_phis_before_nonphi:
  !pre d post. d.inst_opcode <> PHI ==>
    LENGTH (collect_phis (pre ++ d::post)) <= LENGTH pre
Proof
  Induct >> simp[collect_phis_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[collect_phis_def]
QED

Theorem local_adjacent_use_predecessor:
  wf_function f /\ d.inst_opcode = ADD /\ d.inst_outputs = [x] /\
  (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
    MEM (Var x) j.inst_operands ==>
    ?pre post. bb.bb_instructions = pre ++ [d;j] ++ post) /\
  var_used_at f.fn_blocks l i x ==>
  0 < i /\ var_defined_at f.fn_blocks l (i - 1) x /\
  (!bb. lookup_block l f.fn_blocks = SOME bb ==>
    LENGTH (collect_phis bb.bb_instructions) < i)
Proof
  strip_tac >> gvs[var_used_at_def, inst_uses_def, MEM_operand_vars_eq_Var] >>
  `MEM bb f.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  first_x_assum drule_all >> strip_tac >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  `i = LENGTH pre + 1` by metis_tac[distinct_adjacent_read_index] >>
  `EL (i - 1) bb.bb_instructions = d` by
    (qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_APPEND_EQN]) >>
  simp[var_defined_at_def, inst_defs_def] >>
  conj_tac >- gvs[] >>
  `LENGTH (collect_phis (pre ++ d::EL i bb.bb_instructions::post)) <= LENGTH pre` by
    (irule collect_phis_before_nonphi >> simp[]) >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, APPEND] >>
  gvs[]
QED

Theorem local_adjacent_not_live:
  wf_function f /\ d.inst_opcode = ADD /\ d.inst_outputs = [x] /\
  (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
    MEM (Var x) j.inst_operands ==>
    ?pre post. bb.bb_instructions = pre ++ [d;j] ++ post) /\
  (i = 0 \/ ?bb. lookup_block l f.fn_blocks = SOME bb /\
    i = LENGTH (collect_phis bb.bb_instructions)) ==>
  ~MEM x (live_vars_at (liveness_analyze f) l i)
Proof
  strip_tac >> strip_tac >>
  `!a k. var_used_at f.fn_blocks a k x ==>
    0 < k /\ var_defined_at f.fn_blocks a (k - 1) x /\
    (!b. lookup_block a f.fn_blocks = SOME b ==>
      LENGTH (collect_phis b.bb_instructions) < k)` by
    (rpt gen_tac >> disch_tac >> irule local_adjacent_use_predecessor >>
     goal_assum (drule_at Any) >> simp[] >> qexists_tac `d` >> simp[]) >>
  `~var_used_at f.fn_blocks l i x` by
    (strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
     metis_tac[prim_recTheory.LESS_REFL]) >>
  `?ps. cfg_exec_path (cfg_analyze f) ((l,i)::ps) /\
     used_before_defined f.fn_blocks x ((l,i)::ps)` by
    (irule (SIMP_RULE (srw_ss()) [LET_THM] liveness_recompute_sound) >>
     gvs[liveness_analyze_def]) >>
  metis_tac[adjacent_definition_path_exclusion]
QED

Theorem selected_phi_lookup_block:
  !bbs l vs live x.
    ALOOKUP (current_live_in_after_phis live bbs) l = SOME vs /\ MEM x vs ==>
    ?bb. lookup_block l bbs = SOME bb
Proof
  Induct >> simp[current_live_in_after_phis_def] >> rpt gen_tac >>
  Cases_on `h.bb_label = l` >> simp[lookup_block_def, FIND_thm] >>
  strip_tac >> metis_tac[lookup_block_def]
QED

Theorem local_adjacent_selected_not_live:
  wf_function f /\ d.inst_opcode = ADD /\ d.inst_outputs = [x] /\
  (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
    MEM (Var x) j.inst_operands ==>
    ?pre post. bb.bb_instructions = pre ++ [d;j] ++ post) /\
  ALOOKUP (select_current_live_in had_phis (liveness_analyze f) f) l = SOME vs ==>
  ~MEM x vs
Proof
  strip_tac >> strip_tac >> reverse (Cases_on `had_phis`)
  >- (gvs[select_current_live_in_def, current_query_map_def] >>
      drule ALOOKUP_MEM >> simp[MEM_MAP] >> strip_tac >> gvs[] >>
      `MEM x (live_vars_at (liveness_analyze f) l 0)` by
        gvs[liveness_analyze_def, liveness_recompute_boundary_entry] >>
      metis_tac[local_adjacent_not_live]) >>
  `?bb. lookup_block l f.fn_blocks = SOME bb` by
    (irule selected_phi_lookup_block >>
     gvs[select_current_live_in_def] >> metis_tac[]) >>
  `MEM x (live_vars_at (liveness_analyze f) l
     (LENGTH (collect_phis bb.bb_instructions)))` by
    metis_tac[current_selected_live_phi_cut] >>
  metis_tac[local_adjacent_not_live]
QED
