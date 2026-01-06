(* 
 * Simplify-CFG Correctness
 *
 * Pass-level correctness theorems for simplify-cfg.
 *)

Theory scfgCorrect
Ancestors
  scfgMergeCorrect scfgTransform list relation

(* ===== CFG/Lookup Helpers ===== *)

Theorem lookup_block_label:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> fs[]
QED

Theorem lookup_block_MEM:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> MEM bb blocks
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> fs[] >>
  res_tac >> simp[]
QED

Theorem lookup_block_at_hd:
  !lbl blocks bb.
    blocks <> [] /\
    lbl = (HD blocks).bb_label /\
    lookup_block lbl blocks = SOME bb ==>
    bb = HD blocks
Proof
  Cases_on `blocks` >> simp[lookup_block_def]
QED

Theorem lookup_block_filter:
  !P lbl blocks bb.
    lookup_block lbl blocks = SOME bb /\ P bb ==>
    lookup_block lbl (FILTER P blocks) = SOME bb
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> fs[]
  >- (fs[] >> simp[lookup_block_def])
  >- (first_x_assum drule >> simp[])
QED

Theorem lookup_block_filter_none:
  !P lbl blocks.
    lookup_block lbl blocks = NONE ==> lookup_block lbl (FILTER P blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> fs[]
QED

Theorem lookup_block_simplify_phi_block:
  !lbl blocks fn' bb.
    lookup_block lbl blocks = SOME bb ==>
    lookup_block lbl
      (MAP (\\bb. simplify_phi_block (pred_labels fn' bb.bb_label) bb) blocks) =
    SOME (simplify_phi_block (pred_labels fn' lbl) bb)
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> fs[lookup_block_label]
  >- simp[lookup_block_def, simplify_phi_block_label]
  >- (first_x_assum drule >> simp[])
QED

Theorem lookup_block_simplify_phi_block_none:
  !lbl blocks fn'.
    lookup_block lbl blocks = NONE ==>
    lookup_block lbl
      (MAP (\\bb. simplify_phi_block (pred_labels fn' bb.bb_label) bb) blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> fs[lookup_block_def, simplify_phi_block_label]
QED

Theorem pred_labels_mem_from_edge:
  !fn bb lbl.
    MEM bb fn.fn_blocks /\ MEM lbl (block_successors bb) ==>
    MEM bb.bb_label (pred_labels fn lbl)
Proof
  rw[pred_labels_def] >>
  simp[MEM_MAP] >>
  qexists_tac `bb` >>
  simp[MEM_FILTER]
QED

Theorem pred_labels_subset:
  !fn fn' lbl pred.
    (!bb. MEM bb fn'.fn_blocks ==> MEM bb fn.fn_blocks) /\
    MEM pred (pred_labels fn' lbl) ==>
    MEM pred (pred_labels fn lbl)
Proof
  rw[pred_labels_def] >>
  fs[MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem pred_labels_keep_reachable:
  !fn entry lbl prev keep.
    keep = FILTER (\\bb. reachable_label fn entry bb.bb_label) fn.fn_blocks /\
    MEM prev (pred_labels fn lbl) /\
    reachable_label fn entry prev ==>
    MEM prev (pred_labels (fn with fn_blocks := keep) lbl)
Proof
  rpt strip_tac >>
  fs[pred_labels_def, MEM_MAP, MEM_FILTER] >>
  qexists_tac `bb` >>
  simp[MEM_FILTER] >>
  metis_tac[]
QED

Theorem block_last_inst_terminator:
  !bb idx inst.
    block_terminator_last bb /\
    get_instruction bb idx = SOME inst /\
    is_terminator inst.inst_opcode ==>
    block_last_inst bb = SOME inst
Proof
  rpt strip_tac >>
  fs[block_terminator_last_def] >>
  qpat_x_assum `get_instruction _ _ = _` mp_tac >>
  simp[get_instruction_def] >> strip_tac >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> fs[]) >>
  simp[block_last_inst_def, listTheory.LAST_EL, arithmeticTheory.PRE_SUB1] >>
  simp[] >> metis_tac[]
QED

Theorem run_block_ok_successor:
  !fn bb s s'.
    cfg_wf fn /\
    MEM bb fn.fn_blocks /\
    run_block fn bb s = OK s' /\
    ~s'.vs_halted ==>
    MEM s'.vs_current_bb (block_successors bb)
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  Cases_on `r` >> simp[] >- (
    (* Terminator case *)
    qpat_x_assum `step_in_block _ _ _ = _` mp_tac >>
    simp[step_in_block_def] >>
    Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
    Cases_on `step_inst x s` >> simp[] >>
    Cases_on `is_terminator x.inst_opcode` >> simp[] >>
    strip_tac >>
    `block_terminator_last bb` by
      (fs[cfg_wf_def] >> metis_tac[]) >>
    drule_at (Pos last) block_last_inst_terminator >> simp[] >>
    simp[block_successors_def] >>
    drule_at (Pos last) step_inst_terminator_successor >> simp[]
  ) >>
  (* Non-terminal case *)
  first_x_assum irule >> simp[]
QED

Theorem reachable_label_step:
  !fn entry src dst.
    reachable_label fn entry src /\ cfg_edge fn src dst ==>
    reachable_label fn entry dst
Proof
  rw[reachable_label_def] >>
  irule relationTheory.RTC_TRANS >>
  qexists_tac `src` >>
  conj_tac >- simp[] >>
  irule (CONJUNCT2 (SPEC (cfg_edge fn) relationTheory.RTC_RULES)) >>
  simp[]
QED

Theorem run_function_remove_unreachable_equiv:
  !fuel fn s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    reachable_label fn (entry_label fn) s.vs_current_bb /\
    (s.vs_prev_bb = NONE ==> s.vs_current_bb = entry_label fn) /\
    (s.vs_prev_bb = SOME prev ==> MEM prev (pred_labels fn s.vs_current_bb)) /\
    (s.vs_prev_bb = SOME prev ==> reachable_label fn (entry_label fn) prev)
  ==>
    result_equiv_cfg (run_function fuel fn s)
                     (run_function fuel (remove_unreachable_blocks fn) s)
Proof
  Induct_on `fuel` >> rpt strip_tac
  >- simp[run_function_def, result_equiv_cfg_def] >>
  simp[Once run_function_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (
    qabbrev_tac `entry = entry_label fn` >>
    qabbrev_tac `keep = FILTER (\\bb. reachable_label fn entry bb.bb_label) fn.fn_blocks` >>
    qabbrev_tac `fn_keep = fn with fn_blocks := keep` >>
    qabbrev_tac `fix = MAP (\\bb. simplify_phi_block (pred_labels fn_keep bb.bb_label) bb) keep` >>
    `remove_unreachable_blocks fn = fn with fn_blocks := fix` by
      (simp[remove_unreachable_blocks_def, Abbr`entry`, Abbr`keep`,
            Abbr`fn_keep`, Abbr`fix`, LET_THM, cfg_wf_def]) >>
    simp[Once run_function_def] >>
    `lookup_block s.vs_current_bb keep = NONE` by
      (irule lookup_block_filter_none >> simp[Abbr`keep`]) >>
    `lookup_block s.vs_current_bb fix = NONE` by
      (drule lookup_block_simplify_phi_block_none >> simp[Abbr`fix`]) >>
    simp[result_equiv_cfg_def]
  )
  >- (
    rename1 `lookup_block _ _ = SOME bb` >>
    qabbrev_tac `entry = entry_label fn` >>
    qabbrev_tac `keep = FILTER (\\bb. reachable_label fn entry bb.bb_label) fn.fn_blocks` >>
    qabbrev_tac `fn_keep = fn with fn_blocks := keep` >>
    qabbrev_tac `fix = MAP (\\bb. simplify_phi_block (pred_labels fn_keep bb.bb_label) bb) keep` >>
    `remove_unreachable_blocks fn = fn with fn_blocks := fix` by
      (simp[remove_unreachable_blocks_def, Abbr`entry`, Abbr`keep`,
            Abbr`fn_keep`, Abbr`fix`, LET_THM, cfg_wf_def]) >>
    `lookup_block s.vs_current_bb keep = SOME bb` by (
      irule lookup_block_filter >> simp[Abbr`keep`] >>
      `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
      simp[]
    ) >>
    `lookup_block s.vs_current_bb fix =
       SOME (simplify_phi_block (pred_labels fn_keep s.vs_current_bb) bb)` by
      (simp[Abbr`fix`] >> drule lookup_block_simplify_phi_block >> simp[]) >>
    simp[Once run_function_def] >>
    Cases_on `s.vs_prev_bb`
    >- (
      `s.vs_current_bb = entry` by metis_tac[] >>
      `bb = HD fn.fn_blocks` by
        (irule lookup_block_at_hd >> simp[Abbr`entry`, cfg_wf_def]) >>
      `block_has_no_phi bb` by
        (simp[Abbr`entry`] >> metis_tac[phi_fn_wf_entry_no_phi]) >>
      `simplify_phi_block (pred_labels fn_keep bb.bb_label) bb = bb` by
        simp[simplify_phi_block_no_phi] >>
      simp[] >>
      Cases_on `run_block fn bb s` >> simp[result_equiv_cfg_def] >>
      rename1 `run_block fn bb s = OK v` >>
      Cases_on `v.vs_halted` >> simp[result_equiv_cfg_def] >>
      `v.vs_prev_bb = SOME s.vs_current_bb` by
        (drule_all run_block_ok_prev_bb >> simp[]) >>
      `MEM s.vs_current_bb (pred_labels fn v.vs_current_bb)` by (
        `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        drule_all run_block_ok_successor >> strip_tac >>
        drule pred_labels_mem_from_edge >> simp[]
      ) >>
      `reachable_label fn entry v.vs_current_bb` by (
        `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        drule_all run_block_ok_successor >> strip_tac >>
        `cfg_edge fn s.vs_current_bb v.vs_current_bb` by
          (rw[cfg_edge_def] >> qexists_tac `bb` >> simp[]) >>
        metis_tac[reachable_label_step]
      ) >>
      first_x_assum irule >>
      simp[Abbr`entry`] >>
      metis_tac[]
    )
    >- (
      rename1 `s.vs_prev_bb = SOME prev` >>
      `result_equiv_cfg (run_block fn bb s)
         (run_block fn (simplify_phi_block (pred_labels fn_keep bb.bb_label) bb) s)` by (
        `phi_block_wf (pred_labels fn bb.bb_label) bb` by
          (irule phi_fn_wf_block >> simp[]) >>
        `MEM prev (pred_labels fn_keep bb.bb_label)` by
          (irule pred_labels_keep_reachable >> simp[Abbr`keep`]) >>
        `!lbl. MEM lbl (pred_labels fn_keep bb.bb_label) ==>
              MEM lbl (pred_labels fn bb.bb_label)` by
          (rpt strip_tac >>
           irule pred_labels_subset >>
           simp[Abbr`fn_keep`] >>
           metis_tac[]) >>
        irule run_block_simplify_phi >>
        simp[] >> metis_tac[]
      ) >>
      Cases_on `run_block fn bb s` >>
      Cases_on `run_block fn (simplify_phi_block (pred_labels fn_keep bb.bb_label) bb) s` >>
      gvs[result_equiv_cfg_def] >>
      rename1 `run_block fn bb s = OK v` >>
      `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_cfg_def] >>
      Cases_on `v.vs_halted` >> gvs[result_equiv_cfg_def] >>
      `run_block fn (simplify_phi_block (pred_labels fn_keep bb.bb_label) bb) s = OK v` by (
        irule run_block_simplify_phi_ok >>
        `phi_block_wf (pred_labels fn bb.bb_label) bb` by
          (irule phi_fn_wf_block >> simp[]) >>
        `MEM prev (pred_labels fn_keep bb.bb_label)` by
          (irule pred_labels_keep_reachable >> simp[Abbr`keep`]) >>
        `!lbl. MEM lbl (pred_labels fn_keep bb.bb_label) ==>
              MEM lbl (pred_labels fn bb.bb_label)` by
          (rpt strip_tac >>
           irule pred_labels_subset >>
           simp[Abbr`fn_keep`] >>
           metis_tac[]) >>
        simp[]
      ) >>
      `v.vs_prev_bb = SOME s.vs_current_bb` by
        (drule_all run_block_ok_prev_bb >> simp[]) >>
      `MEM s.vs_current_bb (pred_labels fn v.vs_current_bb)` by (
        `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        drule_all run_block_ok_successor >> strip_tac >>
        drule pred_labels_mem_from_edge >> simp[]
      ) >>
      `reachable_label fn entry v.vs_current_bb` by (
        `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
        drule_all run_block_ok_successor >> strip_tac >>
        `cfg_edge fn s.vs_current_bb v.vs_current_bb` by
          (rw[cfg_edge_def] >> qexists_tac `bb` >> simp[]) >>
        metis_tac[reachable_label_step]
      ) >>
      first_x_assum irule >>
      simp[Abbr`entry`] >>
      metis_tac[]
    )
  )
QED

(* ===== Simplify-CFG Step Correctness (Skeletons) ===== *)

Theorem remove_unreachable_blocks_correct:
  !fn s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE ==>
    run_function_equiv_cfg fn (remove_unreachable_blocks fn) s
Proof
  rw[run_function_equiv_cfg_def]
  >- (
    qexists_tac `fuel` >>
    `result_equiv_cfg (run_function fuel fn s)
                      (run_function fuel (remove_unreachable_blocks fn) s)` by (
      irule run_function_remove_unreachable_equiv >>
      simp[reachable_label_def, relationTheory.RTC_REFL]
    ) >>
    Cases_on `run_function fuel fn s` >>
    gvs[terminates_def, result_equiv_cfg_def]
  )
  >- (
    qexists_tac `fuel'` >>
    `result_equiv_cfg (run_function fuel' fn s)
                      (run_function fuel' (remove_unreachable_blocks fn) s)` by (
      irule run_function_remove_unreachable_equiv >>
      simp[reachable_label_def, relationTheory.RTC_REFL]
    ) >>
    Cases_on `run_function fuel' (remove_unreachable_blocks fn) s` >>
    gvs[terminates_def, result_equiv_cfg_def]
  )
QED

Theorem simplify_cfg_step_correct:
  !fn fn' s.
    simplify_cfg_step fn fn' /\
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 ==>
    run_function_equiv_cfg fn fn' s
Proof
  cheat
QED

Theorem simplify_cfg_correct:
  !fn fn' s.
    simplify_cfg fn fn' /\
    cfg_wf fn /\
    phi_fn_wf fn /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 ==>
    run_function_equiv_cfg fn fn' s
Proof
  cheat
QED

val _ = export_theory();
