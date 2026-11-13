Theory o1LabelFlowPhiPruning
Ancestors
  makeSsaDefs list alist

Theorem process_frontiers_supply_not_live:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
    (!l vs. ALOOKUP li l = SOME vs ==> ~MEM v vs) /\
    process_frontiers_supply s v pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    bbs' = bbs /\ rest' = rest /\ s' = s
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP li h` >>
  Cases_on `MEM h hp` >> gvs[process_frontiers_supply_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem insert_phis_for_var_supply_not_live:
  !s v df pm li bbs work hp.
    (!l vs. ALOOKUP li l = SOME vs ==> ~MEM v vs) ==>
    insert_phis_for_var_supply s v df pm li bbs work hp = (bbs,s)
Proof
  recInduct insert_phis_for_var_supply_ind >> conj_tac
  >- simp[insert_phis_for_var_supply_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once insert_phis_for_var_supply_def] >>
  pairarg_tac >> gvs[] >>
  drule_all process_frontiers_supply_not_live >> strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED
