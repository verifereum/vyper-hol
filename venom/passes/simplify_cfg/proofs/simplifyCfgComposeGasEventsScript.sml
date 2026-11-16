Theory simplifyCfgComposeGasEvents
Ancestors
  simplifyCfgGasEventBoundary simplifyCfgBypassGasEvents
  simplifyCfgCleanupGasEvents simplifyCfgRoundSemantics
  simplifyCfgCollapseSemantics simplifyCfgStaticInterface simplifyCfgSimTools
  simplifyCfgBypassPrecondition simplifyCfgBypassClosure simplifyCfgMergeClosure
  simplifyCfgMergePaths simplifyCfgBypassWrapper
  simplifyCfgDefs o1PassLift gasEvents venomExecProofs venomWf
  simplifyCfgGeneratedSubst list

Theorem scfg_gas_transport_compose:
  (!n. ?m e. gas_events_blocks m C g s = gas_events_blocks n C f s ++ e /\
    (terminates (run_blocks n C f s) ==> e = [] /\
      frame_result_rel (run_blocks n C f s) (run_blocks m C g s))) /\
  (!n. ?m e. gas_events_blocks m C h s = gas_events_blocks n C g s ++ e /\
    (terminates (run_blocks n C g s) ==> e = [] /\
      frame_result_rel (run_blocks n C g s) (run_blocks m C h s))) ==>
  !n. ?m e. gas_events_blocks m C h s = gas_events_blocks n C f s ++ e /\
    (terminates (run_blocks n C f s) ==> e = [] /\
      frame_result_rel (run_blocks n C f s) (run_blocks m C h s))
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `!n. ?m e. gas_events_blocks m C g s = _ /\ _`
    (qspec_then `n` strip_assume_tac) >>
  qpat_x_assum `!n. ?m e. gas_events_blocks m C h s = _ /\ _`
    (qspec_then `m` strip_assume_tac) >>
  qexistsl_tac [`m'`, `e ++ e'`] >> simp[APPEND_ASSOC] >>
  metis_tac[frame_result_rel_terminates, frame_result_rel_trans]
QED

Theorem scfg_collapse_relation:
  (!f. scfg_normalized f ==> R f f) /\
  (!f g h. R f g /\ R g h ==> R f h) /\
  (!f a b. scfg_chain_hyp f a b ==> R f (scfg_chain f a b)) /\
  (!f a b g. scfg_bypass_hyp f a b g ==> R f g) ==>
  (!fn lm visited lbl. scfg_normalized fn ==>
    R fn (FST (collapse_dfs fn lm visited lbl))) /\
  (!fn lm visited succs. scfg_normalized fn ==>
    R fn (FST (collapse_dfs_succs fn lm visited succs)))
Proof
  strip_tac >> ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- simp[collapse_dfs_def]
  >> suspend "succs"
QED

Resume scfg_collapse_relation[dfs]:
  rpt strip_tac >> simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- simp[] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_member_label] >>
  namedCases_on `bb_succs bb` ["", "s1 rest"]
  >- (Cases_on `MEM lbl visited` >> simp[try_bypass_def]) >>
  namedCases_on `rest` ["", "s2 rest2"]
  >- (Cases_on `lookup_block s1 fn.fn_blocks`
      >- (Cases_on `MEM lbl visited` >> simp[]) >>
      rename1 `lookup_block s1 fn.fn_blocks = SOME next_bb` >>
      Cases_on `can_merge_blocks fn bb next_bb`
      >- suspend "merge" >>
      Cases_on `MEM lbl visited` >> simp[]) >>
  suspend "bypass"
QED

Resume scfg_collapse_relation[merge]:
  gvs[] >>
  `next_bb.bb_label = s1` by metis_tac[lookup_block_member_label] >>
  `scfg_chain_hyp fn bb next_bb` by
    (simp[scfg_chain_hyp_def] >> metis_tac[]) >>
  `R fn (scfg_chain fn bb next_bb)` by metis_tac[] >>
  `scfg_normalized (scfg_chain fn bb next_bb)` by metis_tac[scfg_chain_normalized] >>
  gvs[GSYM scfg_chain_def] >> metis_tac[]
QED

Resume scfg_collapse_relation[bypass]:
  Cases_on `try_bypass fn lm bb (s1::s2::rest2)` >> PairCases_on `r` >>
  `scfg_collapse_contract fn q` by
    (irule scfg_collapse_bypass >> simp[] >>
     qexistsl_tac [`bb`, `s1::s2::rest2`, `r1`, `lm`, `r0`] >> simp[]) >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  `R fn q` by
    metis_tac[scfg_try_bypass_choice] >>
  Cases_on `r1` >> gvs[] >>
  Cases_on `MEM bb.bb_label visited` >> gvs[] >> metis_tac[]
QED

Resume scfg_collapse_relation[succs]:
  rpt strip_tac >> simp[Once collapse_dfs_def] >>
  Cases_on `collapse_dfs fn lm visited lbl` >> PairCases_on `r` >> gvs[] >>
  `scfg_normalized q` by
    metis_tac[scfg_collapse_joint, scfg_collapse_contract_def, pairTheory.FST] >>
  pure_once_rewrite_tac[collapse_dfs_def] >> simp[] >> metis_tac[]
QED
Finalise scfg_collapse_relation

Theorem scfg_gas_transport_refl:
  !n. ?m e. gas_events_blocks m C f s = gas_events_blocks n C f s ++ e /\
    (terminates (run_blocks n C f s) ==> e = [] /\
      frame_result_rel (run_blocks n C f s) (run_blocks m C f s))
Proof
  gen_tac >> qexistsl_tac [`n`, `[]`] >> simp[] >> strip_tac >>
  irule frame_result_rel_refl >> simp[run_blocks_not_OK]
QED

Theorem scfg_collapse_gas_joint:
  (!fn lm visited lbl. scfg_normalized fn ==>
    fn_entry_label (FST (collapse_dfs fn lm visited lbl)) = fn_entry_label fn /\
    (!C s. fn_entry_state fn s ==> !n. ?m e.
      gas_events_blocks m C (FST (collapse_dfs fn lm visited lbl)) s =
        gas_events_blocks n C fn s ++ e /\
      (terminates (run_blocks n C fn s) ==> e = [] /\
        frame_result_rel (run_blocks n C fn s)
          (run_blocks m C (FST (collapse_dfs fn lm visited lbl)) s)))) /\
  (!fn lm visited succs. scfg_normalized fn ==>
    fn_entry_label (FST (collapse_dfs_succs fn lm visited succs)) = fn_entry_label fn /\
    (!C s. fn_entry_state fn s ==> !n. ?m e.
      gas_events_blocks m C (FST (collapse_dfs_succs fn lm visited succs)) s =
        gas_events_blocks n C fn s ++ e /\
      (terminates (run_blocks n C fn s) ==> e = [] /\
        frame_result_rel (run_blocks n C fn s)
          (run_blocks m C (FST (collapse_dfs_succs fn lm visited succs)) s))))
Proof
  ho_match_mp_tac scfg_collapse_relation >> rpt conj_tac
  >- simp[scfg_gas_transport_refl]
  >- (rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >> irule scfg_gas_transport_compose >>
      qexists_tac `g` >> conj_tac >- metis_tac[] >>
      `fn_entry_state g s` by fs[fn_entry_state_def] >> metis_tac[])
  >- (rpt strip_tac >- metis_tac[scfg_chain_entry_eq] >>
      metis_tac[scfg_chain_gas_entry_forward]) >>
  rpt strip_tac >- metis_tac[scfg_bypass_entry_eq] >>
  metis_tac[scfg_bypass_gas_entry_forward]
QED

Theorem scfg_cleanup_gas_forward:
  scfg_static f /\ fn_entry_state f s ==> !n. ?m e.
    gas_events_blocks m C (fix_all_phis (remove_unreachable_blocks f)) s =
      gas_events_blocks n C f s ++ e /\
    (terminates (run_blocks n C f s) ==> e = [] /\
      frame_result_rel (run_blocks n C f s)
        (run_blocks m C (fix_all_phis (remove_unreachable_blocks f)) s))
Proof
  strip_tac >> gen_tac >> qexistsl_tac [`n`, `[]`] >>
  `gas_events_blocks n C (fix_all_phis (remove_unreachable_blocks f)) s =
     gas_events_blocks n C f s /\
   run_blocks n C (fix_all_phis (remove_unreachable_blocks f)) s = run_blocks n C f s` by
    (irule scfg_cleanup_entry_observation >> fs[scfg_static_def]) >>
  simp[] >> strip_tac >> irule frame_result_rel_refl >> simp[run_blocks_not_OK]
QED

Theorem scfg_round_gas_forward:
  scfg_static fn /\ fn_entry_state fn s ==> !n. ?m e.
    gas_events_blocks m C (FST (simplify_cfg_round_with_labels fn)) s =
      gas_events_blocks n C fn s ++ e /\
    (terminates (run_blocks n C fn s) ==> e = [] /\
      frame_result_rel (run_blocks n C fn s)
        (run_blocks m C (FST (simplify_cfg_round_with_labels fn)) s))
Proof
  strip_tac >>
  `?lbl. fn_entry_label fn = SOME lbl` by metis_tac[fn_entry_state_def] >>
  qabbrev_tac `clean = fix_all_phis (remove_unreachable_blocks fn)` >>
  `scfg_normalized clean` by metis_tac[scfg_normalized_cleanup] >>
  `fn_entry_label clean = fn_entry_label fn` by metis_tac[scfg_static_cleanup_entry] >>
  `fn_entry_state clean s` by fs[fn_entry_state_def] >>
  Cases_on `collapse_dfs clean [] [] lbl` >> PairCases_on `r` >>
  `scfg_collapse_contract clean q` by metis_tac[scfg_collapse_joint, pairTheory.FST] >>
  `scfg_normalized q` by fs[scfg_collapse_contract_def] >>
  `scfg_static q` by metis_tac[scfg_normalized_static] >>
  `fn_entry_state q s` by fs[fn_entry_state_def, scfg_collapse_contract_def] >>
  `ALL_DISTINCT (fn_labels clean)` by
    fs[scfg_normalized_def, scfg_static_def, wf_function_def] >>
  `subst_block_labels_fn r0 q = q` by metis_tac[scfg_collapse_subst_identity] >>
  `!n. ?m e. gas_events_blocks m C q s = gas_events_blocks n C clean s ++ e /\
    (terminates (run_blocks n C clean s) ==> e=[] /\
      frame_result_rel (run_blocks n C clean s) (run_blocks m C q s))` by
    metis_tac[scfg_collapse_gas_joint, pairTheory.FST] >>
  `FST (simplify_cfg_round_with_labels fn) =
    fix_all_phis (remove_unreachable_blocks q)` by
    (qpat_x_assum `Abbrev (clean = _)` (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[simplify_cfg_round_with_labels_def]) >>
  pop_assum SUBST1_TAC >>
  irule scfg_gas_transport_compose >> qexists_tac `clean` >>
  conj_tac >- metis_tac[scfg_cleanup_gas_forward] >>
  irule scfg_gas_transport_compose >> qexists_tac `q` >>
  simp[scfg_cleanup_gas_forward]
QED

Theorem scfg_iter_gas_forward:
  !k fn. scfg_static fn /\ fn_entry_state fn s ==> !n. ?m e.
    gas_events_blocks m C (FST (simplify_cfg_iter_with_labels k fn)) s =
      gas_events_blocks n C fn s ++ e /\
    (terminates (run_blocks n C fn s) ==> e = [] /\
      frame_result_rel (run_blocks n C fn s)
        (run_blocks m C (FST (simplify_cfg_iter_with_labels k fn)) s))
Proof
  Induct >- simp[simplify_cfg_iter_with_labels_def, scfg_gas_transport_refl] >>
  gen_tac >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  `scfg_collapse_contract fn q` by metis_tac[scfg_round_contract, pairTheory.FST] >>
  Cases_on `q.fn_blocks = fn.fn_blocks`
  >- simp[simplify_cfg_iter_with_labels_def, scfg_gas_transport_refl] >>
  `scfg_static q` by metis_tac[scfg_collapse_contract_def, scfg_normalized_static] >>
  `fn_entry_state q s` by fs[scfg_collapse_contract_def, fn_entry_state_def] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `simplify_cfg_iter_with_labels k q` >>
  simp[simplify_cfg_iter_with_labels_def] >>
  irule scfg_gas_transport_compose >> qexists_tac `q` >>
  conj_tac >- metis_tac[scfg_round_gas_forward, pairTheory.FST] >> fs[]
QED

Theorem scfg_fn_gas_forward:
  scfg_static fn /\ fn_entry_state fn s ==> !n. ?m e.
    gas_events_blocks m C (simplify_cfg_fn fn) s = gas_events_blocks n C fn s ++ e /\
    (terminates (run_blocks n C fn s) ==> e = [] /\
      frame_result_rel (run_blocks n C fn s) (run_blocks m C (simplify_cfg_fn fn) s))
Proof
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def, scfg_iter_gas_forward]
QED
