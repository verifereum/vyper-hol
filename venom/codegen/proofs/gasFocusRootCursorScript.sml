Theory gasFocusRootCursor
Ancestors contextRawReachable contextCodegenRel venomState

(* The entry rule installs its own cursor before observing the root. *)
Theorem focus_raw_reachable_root_cursor:
  !v C fn inst s. raw_reachable v C fn inst s ==>
    !root lbl. v = root with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> ==>
    raw_reachable root C fn inst s
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >> metis_tac[raw_reachable_rules]
QED
