Theory algebraicOptDominanceProofs
Ancestors
  venomWf venomExecProofs simplifyCfgWfssa list rich_list

(* One shared boundary vertex, including repeated occurrences elsewhere. *)
Theorem ao_fn_path_split:
  !front fn middle back.
    is_fn_path fn (front ++ middle::back) <=>
    is_fn_path fn (front ++ [middle]) /\ is_fn_path fn (middle::back)
Proof
  Induct >> simp[is_fn_path_def] >>
  rpt gen_tac >> Cases_on `front`
  >- simp[is_fn_path_def] >>
  rule_assum_tac (REWRITE_RULE [APPEND]) >>
  simp[NoAsms, is_fn_path_def] >> metis_tac[]
QED

Theorem ao_dominator_avoiding_prefix:
  !fn d p.
    fn_dominates fn d p /\ d <> p ==>
    ?path. is_fn_path fn path /\ path <> [] /\
      (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
      LAST path = d /\ ~MEM p path
Proof
  rpt strip_tac >>
  qpat_x_assum `fn_dominates fn d p` mp_tac >>
  simp[fn_dominates_def, fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  drule_all is_fn_path_first_arrival >> strip_tac >>
  qpat_x_assum `!path. _` (qspec_then `pre ++ [p]` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `MEM d pre` mp_tac >>
  disch_then (qx_choose_then `front` (qx_choose_then `back` assume_tac) o
    REWRITE_RULE [MEM_SPLIT]) >> gvs[] >>
  qpat_x_assum `is_fn_path fn (_ ++ _)` mp_tac >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  once_rewrite_tac[ao_fn_path_split] >> strip_tac >>
  qexists `front ++ [d]` >> simp[] >>
  Cases_on `front` >> gvs[]
QED

Theorem ao_dominance_interval:
  !fn d p u path.
    fn_dominates fn d p /\ fn_dominates fn p u /\
    is_fn_path fn path /\ path <> [] /\
    HD path = d /\ LAST path = u ==> MEM p path
Proof
  rpt strip_tac >> Cases_on `d = p`
  >- (Cases_on `path` >> gvs[]) >>
  drule_all ao_dominator_avoiding_prefix >>
  disch_then (qx_choose_then `prefix` strip_assume_tac) >>
  `prefix = FRONT prefix ++ [d]` by metis_tac[APPEND_FRONT_LAST] >>
  Cases_on `path` >- gvs[] >> gvs[] >>
  `is_fn_path fn (FRONT prefix ++ LAST prefix::t)` by
    (once_rewrite_tac[ao_fn_path_split] >> metis_tac[]) >>
  qpat_x_assum `fn_dominates fn p _` mp_tac >>
  simp[fn_dominates_def] >> strip_tac >>
  qpat_x_assum `!path. _` (qspec_then `FRONT prefix ++ LAST prefix::t` mp_tac) >>
  simp[] >>
  `~MEM p (FRONT prefix)` by metis_tac[MEM_APPEND] >>
  Cases_on `FRONT prefix` >> gvs[] >>
  Cases_on `t` >> gvs[LAST_APPEND_CONS] >>
  qpat_x_assum `prefix = _` (fn th => once_rewrite_tac[th]) >>
  simp[LAST_DEF] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, LAST_APPEND] >>
  simp[LAST_DEF]
QED

Theorem ao_fn_dominates_trans:
  !fn a b c.
    fn_dominates fn a b /\ fn_dominates fn b c ==> fn_dominates fn a c
Proof
  rpt gen_tac >> rewrite_tac[fn_dominates_def] >> strip_tac >>
  simp[] >> rpt strip_tac >>
  `MEM b path` by metis_tac[] >>
  qpat_x_assum `MEM b path`
    (qx_choose_then `front` (qx_choose_then `back` assume_tac) o
     REWRITE_RULE [MEM_SPLIT]) >>
  `is_fn_path fn (front ++ [b])` by metis_tac[ao_fn_path_split] >>
  `MEM a (front ++ [b])` by
    (first_x_assum irule >> simp[] >> Cases_on `front` >> gvs[]) >>
  gvs[]
QED

Theorem ao_fn_dominates_antisym:
  !fn a b.
    fn_dominates fn a b /\ fn_dominates fn b a ==> a = b
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  drule_all ao_dominator_avoiding_prefix >> strip_tac >>
  fs[fn_dominates_def] >> metis_tac[]
QED
