(*
 * Remove Unused — SSA infrastructure proofs.
 *
 * Key theorem: nop_output_not_used_as_operand
 *   Under wf_ssa + ssa_form, NOP'd variables are never used
 *   as operands. This supplies the fixed erased-variable invariant for
 *   backward GAS-oracle reconstruction.
 *
 * Strategy:
 *   Same block: live_vars_at_uses + live_vars_at_propagate_range gives
 *     v live at def+1, contradicting NOP condition.
 *   Cross block: v live at use block, not killed on path to def block
 *     (SSA single def), so v live at def block exit, contradicting
 *     nop_output_not_live_at_exit.
 *)

Theory removeUnusedSsaProofs
Ancestors
  removeUnusedProofs removeUnusedDefs
  passSimulationDefs passSimulationProps analysisSimProps
  livenessProofs livenessDefs
  dfAnalyzeDefs dfAnalyzeProps dfHelperProps
  venomInstProps venomWf venomExecProps venomExecProofs
  stateEquiv stateEquivProps stateEquivProofs
  execEquivProps cfgTransformProps cfgDefs
  passSharedDefs passSharedProps
  venomInst venomState venomExecSemantics
  indexedLists cfgAnalysisProps pointerConfinedDefs
  worklistDefs list rich_list combin
  venomWfProps

(* ===== Fixpoint bridge: edge_transfer ⊆ live_exit ===== *)


(* ===== NOP output liveness helpers ===== *)

Theorem remove_unused_inst_nop_outputs_not_live[local]:
  !live inst. remove_unused_inst live inst = mk_nop_inst inst ==>
    EVERY (\v. ~MEM v live) inst.inst_outputs
Proof
  rpt gen_tac >> simp[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[mk_nop_inst_def, instruction_component_equality] >>
  rpt strip_tac >> gvs[]
QED

Theorem nop_output_not_live_at_exit:
  !fn lr cfg lbl bb idx inst v.
    wf_function fn /\ ssa_form fn /\
    lr = liveness_analyze fn /\
    cfg = cfg_analyze fn /\
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    remove_unused_inst
      (live_after_at lr lbl idx (LENGTH bb.bb_instructions))
      inst = mk_nop_inst inst /\
    MEM v inst.inst_outputs ==>
    ~MEM v (live_vars_at lr lbl (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >>
  drule remove_unused_inst_nop_outputs_not_live >> strip_tac >>
  gvs[listTheory.EVERY_MEM] >>
  gvs[live_after_at_def] >>
  Cases_on `idx + 1 < LENGTH bb.bb_instructions` >> gvs[] >>
  mp_tac not_live_forward_in_block >>
  disch_then (qspecl_then [`fn`, `lbl`, `bb`, `idx + 1`,
                           `LENGTH bb.bb_instructions`, `v`] mp_tac) >>
  simp[LET_THM] >>
  rpt gen_tac >> simp[inst_defs_def] >>
  spose_not_then strip_assume_tac >> gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `idx < LENGTH bb.bb_instructions` by simp[] >>
  `k = idx` by metis_tac[ssa_form_no_dup_in_block] >>
  gvs[]
QED

(* ===== Main theorem: NOP'd variables not used as operands ===== *)


(* If v is live at block p's exit, v is only defined at d_bb, and p <> d,
   then v is live at p's entry (backward propagation through non-defining block) *)
Theorem live_backward_step[local]:
  !fn v d d_bb p p_bb.
    wf_function fn /\ ssa_form fn /\
    p <> d /\
    lookup_block p fn.fn_blocks = SOME p_bb /\
    fn_reachable fn p /\
    MEM v (live_vars_at (liveness_analyze fn) p
             (LENGTH p_bb.bb_instructions)) /\
    lookup_block d fn.fn_blocks = SOME d_bb /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              MEM v inst.inst_outputs ==> bb = d_bb) ==>
    MEM v (live_vars_at (liveness_analyze fn) p 0)
Proof
  rpt strip_tac >>
  `MEM p_bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!k. k < LENGTH p_bb.bb_instructions ==>
       ~MEM v (inst_defs (EL k p_bb.bb_instructions))` by (
    rpt strip_tac >> gvs[inst_defs_def] >>
    `MEM (EL k p_bb.bb_instructions) p_bb.bb_instructions`
      by metis_tac[MEM_EL] >>
    `p_bb = d_bb` by metis_tac[] >>
    `p = d` by metis_tac[lookup_block_label] >>
    gvs[]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre` by
    (irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  Cases_on `LENGTH p_bb.bb_instructions = 0` >- gvs[] >>
  drule (SIMP_RULE std_ss [LET_THM] live_vars_at_propagate_range) >>
  disch_then (qspecl_then [`p`, `p_bb`, `0`,
                           `LENGTH p_bb.bb_instructions`, `v`] mp_tac) >>
  simp[]
QED

Theorem phi_value_vars_eq_map_snd_phi_pairs[local]:
  !ops. phi_value_vars ops = MAP SND (phi_pairs ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  rw[phi_value_vars_def, phi_pairs_def]
QED

(* Liveness propagates backward along a CFG path from d to n:
   if v is live at entry of LAST(path), v is only defined at d_bb,
   and LAST(path) <> d, then v is live at d's exit.

   SNOC induction: peel off the last node and work backward. *)
Theorem live_backward_along_path[local]:
  !path fn v d d_bb.
    wf_function fn /\ ssa_form fn /\
    is_fn_path fn (d :: path) /\ path <> [] /\
    LAST path <> d /\
    fn_reachable fn d /\
    lookup_block d fn.fn_blocks = SOME d_bb /\
    MEM v (live_vars_at (liveness_analyze fn) (LAST path) 0) /\
    ~MEM v (remove_unused_phi_vars fn) /\
    (* v only defined at d_bb *)
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              MEM v inst.inst_outputs ==> bb = d_bb) ==>
    MEM v (live_vars_at (liveness_analyze fn) d
             (LENGTH d_bb.bb_instructions))
Proof
  ho_match_mp_tac SNOC_INDUCT >> simp[] >> rpt strip_tac >>
  gvs[SNOC_APPEND, listTheory.LAST_APPEND_CONS] >>
  (* After SNOC induction: path was SNOC x path', now x is last node *)
  (* Assumptions have path ++ [x] form; LAST simplified to x *)
  `is_fn_path fn (SNOC x (d :: path))` by simp[SNOC_APPEND] >>
  `fn_cfg_edge fn (LAST (d :: path)) x` by
    metis_tac[is_fn_path_last_edge, listTheory.NOT_NIL_CONS] >>
  `is_fn_path fn (d :: path)` by metis_tac[is_fn_path_init] >>
  qabbrev_tac `p = LAST (d :: path)` >>
  `MEM p (d :: path)` by simp[Abbr `p`, rich_listTheory.MEM_LAST] >>
  `fn_reachable fn p` by
    metis_tac[is_fn_path_all_reachable, HD, listTheory.NOT_NIL_CONS] >>
  `fn_reachable fn x` by metis_tac[fn_reachable_step] >>
  `?x_bb. lookup_block x fn.fn_blocks = SOME x_bb` by
    (irule fn_cfg_edge_target_block >> metis_tac[]) >>
  `?p_bb. lookup_block p fn.fn_blocks = SOME p_bb` by
    (irule fn_reachable_has_block >> simp[]) >>
  (* Protected PHI inputs do not need edge-specific backward propagation. *)
  `!inst. MEM inst (collect_phis x_bb.bb_instructions) ==>
          ~MEM v (MAP SND (phi_pairs inst.inst_operands))` by (
    rpt strip_tac >>
    `MEM v (remove_unused_phi_vars fn)` by (
      simp_tac std_ss [remove_unused_phi_vars_def, listTheory.MEM_FLAT,
                       listTheory.MEM_MAP] >>
      qexists_tac `FLAT (MAP
        (\inst. if inst.inst_opcode = PHI
                then phi_value_vars inst.inst_operands else [])
        x_bb.bb_instructions)` >> conj_tac
      >- (qexists_tac `x_bb` >>
          simp[] >> metis_tac[lookup_block_MEM])
      >- (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
          qexists_tac `phi_value_vars inst.inst_operands` >> conj_tac
          >- (qexists_tac `inst` >> simp[] >>
              metis_tac[collect_phis_mem])
          >- simp[phi_value_vars_eq_map_snd_phi_pairs])) >>
    gvs[]) >>
  (* Set up cfg membership *)
  `MEM x (cfg_analyze fn).cfg_dfs_pre` by
    (irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre` by
    (irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  `MEM x (cfg_succs_of (cfg_analyze fn) p)` by
    (irule fn_cfg_edge_succs >> simp[]) >>
  (* v live at x entry → v live at p exit (cross-block) *)
  `MEM v (live_vars_at (liveness_analyze fn) p
                       (LENGTH p_bb.bb_instructions))` by (
    drule (SIMP_RULE std_ss [LET_THM] live_vars_at_cross_block) >>
    disch_then (qspecl_then [`p`, `p_bb`, `x`, `x_bb`, `v`] mp_tac) >>
    simp[]) >>
  Cases_on `p = d`
  >- (
    `p_bb = d_bb` by
      (`lookup_block d fn.fn_blocks = SOME p_bb` by gvs[] >> gvs[]) >>
    gvs[])
  >- (
    `MEM v (live_vars_at (liveness_analyze fn) p 0)` by
      (irule live_backward_step >> simp[] >>
       metis_tac[]) >>
    `path <> []` by (strip_tac >> gvs[Abbr `p`]) >>
    gvs[Abbr `p`, listTheory.LAST_DEF] >>
    first_x_assum irule >> simp[] >> metis_tac[])
QED

(* Dominator version: d dominates n, d <> n, v live at n entry *)
Theorem live_at_entry_backward_to_dominator[local]:
  !fn v d d_bb n.
    wf_function fn /\ ssa_form fn /\
    fn_dominates fn d n /\ d <> n /\
    lookup_block d fn.fn_blocks = SOME d_bb /\
    MEM v (live_vars_at (liveness_analyze fn) n 0) /\
    ~MEM v (remove_unused_phi_vars fn) /\
    (* v only defined at d_bb *)
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
              MEM v inst.inst_outputs ==> bb = d_bb) ==>
    MEM v (live_vars_at (liveness_analyze fn) d
             (LENGTH d_bb.bb_instructions))
Proof
  rpt strip_tac >>
  `fn_reachable fn n` by gvs[fn_dominates_def] >>
  gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  rename1 `is_fn_path fn path_to_n` >>
  `LAST path_to_n = n` by simp[] >>
  `MEM d path_to_n` by (
    gvs[fn_dominates_def] >>
    first_x_assum (qspec_then `path_to_n` mp_tac) >> simp[]) >>
  drule_all is_fn_path_mem_suffix >> strip_tac >>
  rename1 `is_fn_path fn (d :: suffix)` >>
  `LAST (d :: suffix) = n` by simp[] >>
  Cases_on `suffix` >- gvs[] >>
  `fn_reachable fn d` by (irule fn_dominates_dom_reachable >> metis_tac[]) >>
  irule live_backward_along_path >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `h :: t` >> simp[] >>
  gvs[listTheory.LAST_DEF]
QED

Theorem nop_output_not_used_as_operand:
  !fn v bb inst.
    wf_ssa fn /\ ssa_form fn /\ wf_function fn /\
    v IN single_pass_nop_outputs fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM (Var v) inst.inst_operands ==> F
Proof
  rpt strip_tac >>
  rename1 `wf_ssa func` >>
  (* v is NOP'd at some block B at index idx_b *)
  gvs[single_pass_nop_outputs_def, LET_THM,
      pred_setTheory.IN_BIGUNION, PULL_EXISTS,
      listTheory.MEM_MAP] >>
  rename1 `v IN block_nop_outputs _ def_bb` >>
  gvs[block_nop_outputs_def, LET_THM,
      listTheory.MEM_FLAT, MEM_MAPi, PULL_EXISTS] >>
  rename1 `idx_b < LENGTH def_bb.bb_instructions` >>
  `MEM v (EL idx_b def_bb.bb_instructions).inst_outputs /\
   is_removable (EL idx_b def_bb.bb_instructions) /\
   EVERY (\v. ~MEM v (live_after_at
     (protect_liveness func (remove_unused_phi_vars func)
        (liveness_analyze func))
     def_bb.bb_label idx_b (LENGTH def_bb.bb_instructions)))
     (EL idx_b def_bb.bb_instructions).inst_outputs` by (
    qpat_x_assum `MEM v (if _ then _ else _)` mp_tac >>
    simp[COND_RAND, COND_RATOR]) >>
  `live_after_at
      (protect_liveness func (remove_unused_phi_vars func)
         (liveness_analyze func))
      def_bb.bb_label idx_b (LENGTH def_bb.bb_instructions) =
    remove_unused_phi_vars func ++
      live_after_at (liveness_analyze func) def_bb.bb_label idx_b
        (LENGTH def_bb.bb_instructions)` by (
    irule removeUnusedProofsTheory.live_after_protect_liveness >> simp[]) >>
  `EVERY (\w. ~MEM w (live_after_at (liveness_analyze func)
      def_bb.bb_label idx_b (LENGTH def_bb.bb_instructions)))
      (EL idx_b def_bb.bb_instructions).inst_outputs /\
   ~MEM v (remove_unused_phi_vars func)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  qabbrev_tac `def_inst = EL idx_b def_bb.bb_instructions` >>
  qabbrev_tac `lr = liveness_analyze func` >>
  qabbrev_tac `cfg = cfg_analyze func` >>

  (* lookup_block for both blocks *)
  `lookup_block def_bb.bb_label func.fn_blocks = SOME def_bb` by (
    irule wf_lookup_block >> simp[]) >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by (
    irule wf_lookup_block >> simp[]) >>
  (* v used at (bb, some index) *)
  `MEM v (inst_uses inst)` by (irule operand_var_in_inst_uses >> simp[]) >>
  (* A surviving PHI is an ordinary DFG use.  The single pass protects all
     current PHI inputs, so a removed output cannot be one of them. *)
  Cases_on `inst.inst_opcode = PHI`
  >- (`phi_edge_uses_wf func bb inst` by (
        `def_dominates_uses func` by gvs[wf_ssa_def] >>
        fs[def_dominates_uses_def] >>
        first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >> simp[]) >>
      `MEM v (remove_unused_phi_vars func)` by (
        simp_tac std_ss [remove_unused_phi_vars_def,
          listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
        qexists_tac `FLAT (MAP
          (\i. if i.inst_opcode = PHI
               then phi_value_vars i.inst_operands else [])
          bb.bb_instructions)` >> conj_tac
        >- (qexists_tac `bb` >> simp[])
        >- (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
            qexists_tac `phi_value_vars inst.inst_operands` >> conj_tac
            >- (qexists_tac `inst` >> simp[])
            >- (simp[phi_value_vars_eq_map_snd_phi_pairs] >>
                fs[phi_edge_uses_wf_def] >>
                drule_all phi_well_formed_var_pair >> strip_tac >>
                simp[listTheory.MEM_MAP] >>
                qexists_tac `(lbl,v)` >> simp[]))) >>
      gvs[]) >>
  (* By def_dominates_uses: get dominance of defining block over an ordinary
     use block. *)
  `?def_bb' def_inst'.
     MEM def_bb' func.fn_blocks /\ MEM def_inst' def_bb'.bb_instructions /\
     MEM v def_inst'.inst_outputs /\
     fn_dominates func def_bb'.bb_label bb.bb_label /\
     (def_bb' = bb ==>
       ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
             EL i bb.bb_instructions = def_inst' /\
             EL j bb.bb_instructions = inst)` by (
    `def_dominates_uses func` by gvs[wf_ssa_def] >>
    fs[def_dominates_uses_def] >>
    first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >>
    simp[] >> strip_tac >>
    first_x_assum (qspec_then `v` mp_tac) >>
    simp[def_available_at_def]) >>
  (* The defining block must be def_bb by ssa_form *)
  rename1 `MEM def_bb2 func.fn_blocks` >>
  rename1 `MEM def_inst2 def_bb2.bb_instructions` >>
  `def_bb2 = def_bb /\ def_inst2 = def_inst` by
    metis_tac[ssa_unique_output_block, MEM_EL] >>
  gvs[] >>
  (* Now: fn_dominates fn def_bb.bb_label bb.bb_label *)
  (* Derive reachability: fn_dominates gives fn_reachable bb, and
     since def_bb is on every path to bb, def_bb is also reachable *)
  `fn_reachable func bb.bb_label` by gvs[fn_dominates_def] >>
  `MEM bb.bb_label cfg.cfg_dfs_pre` by (
    simp[Abbr `cfg`] >>
    irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  (* def_bb reachable: dominance → dominator reachable *)
  `fn_reachable func def_bb.bb_label` by (
    irule fn_dominates_dom_reachable >> metis_tac[]) >>
  `MEM def_bb.bb_label cfg.cfg_dfs_pre` by (
    simp[Abbr `cfg`] >>
    irule fn_reachable_in_cfg_dfs_pre >> simp[]) >>
  (* v is not live at SUC idx_b *)
  `~MEM v (live_vars_at lr def_bb.bb_label (SUC idx_b))` by (
    `live_after_at lr def_bb.bb_label idx_b
       (LENGTH def_bb.bb_instructions) =
     live_vars_at lr def_bb.bb_label (SUC idx_b)` by
      simp[live_after_at_suc] >>
    gvs[listTheory.EVERY_MEM]) >>
  (* Case split: same block or different block *)
  Cases_on `def_bb = bb`
  >- (
    (* Same block *)
    fs[] >>
    `i = idx_b` by (
      `i < LENGTH bb.bb_instructions` by simp[] >>
      qspecl_then [`func`, `bb`, `v`, `i`, `idx_b`]
        mp_tac ssa_form_no_dup_in_block >>
      simp[markerTheory.Abbrev_def]) >>
    fs[] >>
    gvs[markerTheory.Abbrev_def] >>
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label j)` by (
      drule live_vars_at_uses >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `j`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >> simp[]) >>
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label (SUC i))` by (
      drule live_vars_at_propagate_range >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `SUC i`,
                               `j`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >>
      disch_then match_mp_tac >>
      simp[] >> rpt strip_tac >>
      CCONTR_TAC >> gvs[inst_defs_def] >>
      `k < LENGTH bb.bb_instructions` by simp[] >>
      qspecl_then [`func`, `bb`, `v`, `i`, `k`]
        mp_tac ssa_form_no_dup_in_block >>
      simp[]) >>
    metis_tac[])
  >- (
    (* Cross block: def_bb dominates bb, v live at bb.
       Unfold abbreviations first (safe: last branch, no leak risk) *)
    gvs[markerTheory.Abbrev_def] >>
    (* Derive: pass NOP'd this instruction *)
    `remove_unused_inst
       (live_after_at (liveness_analyze func) def_bb.bb_label idx_b
          (LENGTH def_bb.bb_instructions))
       def_bb.bb_instructions❲idx_b❳ =
     mk_nop_inst def_bb.bb_instructions❲idx_b❳` by (
      simp[remove_unused_inst_def] >>
      rpt (IF_CASES_TAC >> gvs[])) >>
    (* v not live at block exit *)
    `~MEM v (live_vars_at (liveness_analyze func) def_bb.bb_label
               (LENGTH def_bb.bb_instructions))` by (
      qspecl_then [`func`, `liveness_analyze func`, `cfg_analyze func`,
        `def_bb.bb_label`, `def_bb`, `idx_b`,
        `def_bb.bb_instructions❲idx_b❳`, `v`]
        mp_tac nop_output_not_live_at_exit >>
      simp[]) >>
    (* v is live at use block entry *)
    `?idx_s. idx_s < LENGTH bb.bb_instructions /\
             EL idx_s bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label idx_s)` by (
      drule live_vars_at_uses >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `idx_s`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >> simp[]) >>
    (* Propagate to block entry *)
    `MEM v (live_vars_at (liveness_analyze func) bb.bb_label 0)` by (
      Cases_on `idx_s = 0` >- gvs[] >>
      drule live_vars_at_propagate_range >>
      disch_then (qspecl_then [`bb.bb_label`, `bb`, `0`,
                               `idx_s`, `v`] mp_tac) >>
      simp_tac std_ss [LET_THM] >>
      disch_then match_mp_tac >> simp[] >>
      rpt strip_tac >> CCONTR_TAC >>
      gvs[inst_defs_def] >>
      `k < LENGTH bb.bb_instructions` by simp[] >>
      metis_tac[ssa_unique_output_block, MEM_EL]) >>
    (* v live at use block entry, def_bb dominates use block,
       v only defined at def_bb → v live at def_bb exit — contradiction *)
    `def_bb.bb_label <> bb.bb_label` by (
      strip_tac >> gvs[] >>
      `def_bb = bb` by metis_tac[wf_lookup_block] >> gvs[]) >>
    `MEM v (live_vars_at (liveness_analyze func) def_bb.bb_label
              (LENGTH def_bb.bb_instructions))` by (
      irule live_at_entry_backward_to_dominator >>
      simp[] >>
      conj_tac >- metis_tac[ssa_unique_output_block] >>
      qexists_tac `bb.bb_label` >> simp[]) >>
    metis_tac[])
QED

(* Same-state single-pass correctness removed: reconstruction uses the
   unchanged global operand-exclusion theorem above. *)
