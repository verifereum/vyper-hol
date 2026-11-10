Theory loadElimTemporalDominance
Ancestors
  loadElimDefinitionCuts loadElimNormalizeAvailability simplifyCfgWfssa
  venomExecProofs venomWf venomInst list rich_list

Theorem le_path_splice[local]:
  !pre a tail. is_fn_path fn (pre ++ [a]) /\
    is_fn_path fn (a::tail) ==> is_fn_path fn (pre ++ a::tail)
Proof
  Induct >> simp[] >> Cases_on `pre` >> simp[is_fn_path_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem le_dominating_separator:
  fn_dominates fn a d /\ fn_dominates fn d b /\ a <> d /\
  is_fn_path fn (a::tail) /\ LAST (a::tail) = b ==>
  MEM d (a::tail)
Proof
  strip_tac >>
  `fn_reachable fn a` by metis_tac[fn_dominates_dom_reachable] >>
  fs[fn_reachable_def] >> drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  `fn_entry_label fn = SOME (HD (pre ++ [a]))` by metis_tac[] >>
  `~MEM d pre` by
    (`?db gb. db.bb_label = a /\ gb.bb_label = d` by
       (qexistsl [`<|bb_label := a; bb_instructions := []|>`,
                  `<|bb_label := d; bb_instructions := []|>`] >> simp[]) >>
     metis_tac[le_first_arrival_no_earlier_dominance]) >>
  `is_fn_path fn (pre ++ a::tail)` by metis_tac[le_path_splice] >>
  `HD (pre ++ a::tail) = HD (pre ++ [a])` by
    (Cases_on `pre` >> simp[]) >>
  `LAST (pre ++ a::tail) = b` by
    (pure_rewrite_tac[listTheory.LAST_APPEND_CONS] >> asm_rewrite_tac[]) >>
  `MEM d (pre ++ a::tail)` by
    (qpat_x_assum `fn_dominates fn d b` mp_tac >>
     rewrite_tac[fn_dominates_def] >> strip_tac >>
     first_x_assum (qspec_then `pre ++ a::tail` mp_tac) >> simp[] >> gvs[]) >>
  gvs[MEM_APPEND]
QED
