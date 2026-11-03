Theory simplifyCfgPhiRepair
Ancestors
  simplifyCfgDataflow simplifyCfgLabelProps simplifyCfgStruct simplifyCfgDefs
  venomWf venomExecProofs list rich_list relation

Theorem is_fn_path_first_predecessor:
  (!q. fn_cfg_edge fn q b ==> q = p) ==>
  !path. path <> [] /\ is_fn_path fn path /\ HD path <> b /\ LAST path = b ==>
  ?pre. pre <> [] /\ is_fn_path fn pre /\ HD pre = HD path /\
        LAST pre = p /\ ~MEM b pre
Proof
  strip_tac >> Induct >> simp[] >> qx_gen_tac `x` >>
  Cases_on `path` >> simp[is_fn_path_def] >> rpt strip_tac >>
  rename1 `fn_cfg_edge fn x y` >>
  Cases_on `y = b`
  >- (`x = p` by metis_tac[] >> qexists `[x]` >> simp[is_fn_path_def]) >>
  qpat_x_assum `_ ==> ?pre. _` mp_tac >> simp[] >>
  disch_then (qx_choose_then `pre` strip_assume_tac) >>
  qexists `x::pre` >> simp[is_fn_path_prepend] >>
  Cases_on `pre` >> gvs[]
QED

Theorem unique_predecessor_avoiding_path:
  fn_entry_label fn = SOME entry /\ fn_reachable fn b /\ b <> entry /\
  (!q. fn_cfg_edge fn q b ==> q = p) ==>
  ?path. path <> [] /\ is_fn_path fn path /\ HD path = entry /\
         LAST path = p /\ ~MEM b path
Proof
  strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >> gvs[] >>
  drule is_fn_path_first_predecessor >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> metis_tac[]
QED
