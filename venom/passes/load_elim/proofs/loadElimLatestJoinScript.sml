Theory loadElimLatestJoin
Ancestors
  loadElimActionPlacement loadElimLastWriter loadElimOccurrence list

Theorem le_reached_collected_action_latest_join:
  le_occ_prefix C fn s0 es i s /\ wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) /\
  pa.pa_load_lbl = s.vs_current_bb ==>
  ?before after bb u p.
    es = before ++ [PhiOcc bb u p] ++ after /\
    bb.bb_label = pa.pa_join_lbl /\ before <> [] /\
    (!bb' u' p'. MEM (PhiOcc bb' u' p') after ==> bb'.bb_label <> pa.pa_join_lbl)
Proof
  strip_tac >>
  `?pre bb u p suffix. es = pre ++ PhiOcc bb u p :: suffix /\
     bb.bb_label = pa.pa_join_lbl /\
     EVERY (\e. ~(?b t q. e = PhiOcc b t q /\ b.bb_label = pa.pa_join_lbl)) suffix` by
    (qspecl_then [`\e. ?bb u p. e = PhiOcc bb u p /\ bb.bb_label = pa.pa_join_lbl`, `es`]
       mp_tac le_last_selected_split >> simp[] >>
     impl_tac
     >- (drule_all le_collected_action_occurrence >> strip_tac >>
         simp[MEM_APPEND] >> metis_tac[]) >>
     metis_tac[]) >>
  `pre <> []` by
    (metis_tac[le_reached_collected_action_before_nonempty, APPEND]) >>
  qexistsl_tac [`pre`, `suffix`, `bb`, `u`, `p`] >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[]
QED
