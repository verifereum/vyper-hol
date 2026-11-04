Theory fnPlanLineageEntryWitness
Ancestors
  venomExecProofs venomWf list relation

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
