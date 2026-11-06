Theory fnBlockPlanStaticDfsTrace
Ancestors
  fnPlanLineage stackPlanGen stackPlanTypes list pair pred_set

(* Finite successful execution trees, recording inputs only at newly
   visited existing blocks.  The sibling state matches the planner exactly. *)
Inductive aux_trace:
[~aux_nil:]
  aux_trace lv dfg cfg fn [] visited ps ([],visited,ps) []
[~aux_visited:]
  MEM lbl visited /\
  aux_trace lv dfg cfg fn rest visited ps result tr ==>
  aux_trace lv dfg cfg fn (lbl::rest) visited ps result tr
[~aux_missing:]
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = NONE /\
  aux_trace lv dfg cfg fn rest (lbl::visited) ps result tr ==>
  aux_trace lv dfg cfg fn (lbl::rest) visited ps result tr
[~aux_block:]
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (bops,pout) /\
  succ_trace lv dfg cfg fn pout.ps_stack pout.ps_spilled
    (cfg_succs_of cfg lbl) (lbl::visited) pout (sops,seen,pmid) st /\
  aux_trace lv dfg cfg fn rest seen pmid (rops,final,pend) rt ==>
  aux_trace lv dfg cfg fn (lbl::rest) visited ps
    (bops ++ sops ++ rops,final,pend) ((lbl,ps)::(st ++ rt))
[~succ_nil:]
  succ_trace lv dfg cfg fn ss sp [] visited pg ([],visited,pg) []
[~succ_cons:]
  aux_trace lv dfg cfg fn [succ] visited
    (pg with <| ps_stack := ss; ps_spilled := sp |>)
    (sops,seen,pout) st /\
  succ_trace lv dfg cfg fn ss sp rest seen
    (pg with <| ps_alloc := pout.ps_alloc with
                  sa_free_slots := pg.ps_alloc.sa_free_slots;
                ps_label_counter := pout.ps_label_counter |>)
    (rops,final,pend) rt ==>
  succ_trace lv dfg cfg fn ss sp (succ::rest) visited pg
    (sops ++ rops,final,pend) (st ++ rt)
End

Theorem dfs_trace_erasure:
  (!wl visited ps result tr.
    aux_trace lv dfg cfg fn wl visited ps result tr ==>
    generate_fn_plan_aux lv dfg cfg fn wl visited ps = SOME result) /\
  (!ss sp succs visited pg result tr.
    succ_trace lv dfg cfg fn ss sp succs visited pg result tr ==>
    generate_succs_plan lv dfg cfg fn ss sp succs visited pg = SOME result)
Proof
  ho_match_mp_tac aux_trace_ind >> rpt conj_tac >>
  rpt strip_tac >> simp[Once generate_fn_plan_aux_def]
QED

Theorem aux_trace_nil:
  aux_trace lv dfg cfg fn [] visited ps result tr <=>
  result = ([],visited,ps) /\ tr = []
Proof
  simp[Once aux_trace_cases]
QED

Theorem succ_trace_nil:
  succ_trace lv dfg cfg fn ss sp [] visited pg result tr <=>
  result = ([],visited,pg) /\ tr = []
Proof
  simp[Once (cj 2 aux_trace_cases)]
QED

Theorem aux_trace_visited:
  MEM lbl visited ==>
  (aux_trace lv dfg cfg fn (lbl::rest) visited ps result tr <=>
   aux_trace lv dfg cfg fn rest visited ps result tr)
Proof
  strip_tac >> simp[Once aux_trace_cases]
QED

Theorem aux_trace_missing:
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = NONE ==>
  (aux_trace lv dfg cfg fn (lbl::rest) visited ps result tr <=>
   aux_trace lv dfg cfg fn rest (lbl::visited) ps result tr)
Proof
  strip_tac >> simp[Once aux_trace_cases]
QED

Theorem aux_trace_block:
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  (aux_trace lv dfg cfg fn (lbl::rest) visited ps result tr <=>
   ?bops pout sops seen pmid st rops final pend rt.
     generate_block_plan lv dfg cfg fn bb ps = SOME (bops,pout) /\
     succ_trace lv dfg cfg fn pout.ps_stack pout.ps_spilled
       (cfg_succs_of cfg lbl) (lbl::visited) pout (sops,seen,pmid) st /\
     aux_trace lv dfg cfg fn rest seen pmid (rops,final,pend) rt /\
     result = (bops ++ sops ++ rops,final,pend) /\
     tr = (lbl,ps)::(st ++ rt))
Proof
  strip_tac >> simp[Once aux_trace_cases] >> metis_tac[]
QED

Theorem succ_trace_cons:
  succ_trace lv dfg cfg fn ss sp (succ::rest) visited pg result tr <=>
  ?sops seen pout st rops final pend rt.
    aux_trace lv dfg cfg fn [succ] visited
      (pg with <| ps_stack := ss; ps_spilled := sp |>)
      (sops,seen,pout) st /\
    succ_trace lv dfg cfg fn ss sp rest seen
      (pg with <| ps_alloc := pout.ps_alloc with
                    sa_free_slots := pg.ps_alloc.sa_free_slots;
                  ps_label_counter := pout.ps_label_counter |>)
      (rops,final,pend) rt /\
    result = (sops ++ rops,final,pend) /\ tr = st ++ rt
Proof
  simp[Once (cj 2 aux_trace_cases)] >> metis_tac[]
QED

Theorem aux_trace_block_mem:
  aux_trace lv dfg cfg fn (lbl::rest) visited ps result tr /\
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  MEM (lbl,ps) tr
Proof
  rpt strip_tac >> drule_all aux_trace_block >>
  disch_then (fn th => fs[th]) >> gvs[]
QED

Theorem dfs_trace_exists:
  (!lv dfg cfg fn wl visited ps.
    !result. generate_fn_plan_aux lv dfg cfg fn wl visited ps = SOME result ==>
      ?tr. aux_trace lv dfg cfg fn wl visited ps result tr) /\
  (!lv dfg cfg fn ss sp succs visited pg.
    !result. generate_succs_plan lv dfg cfg fn ss sp succs visited pg = SOME result ==>
      ?tr. succ_trace lv dfg cfg fn ss sp succs visited pg result tr)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[Once generate_fn_plan_aux_def] >>
      simp[aux_trace_nil])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `MEM lbl visited`
      >- (gvs[Once generate_fn_plan_aux_def] >>
          metis_tac[aux_trace_visited]) >>
      Cases_on `lookup_block lbl fn.fn_blocks`
      >- (gvs[Once generate_fn_plan_aux_def] >>
          metis_tac[aux_trace_missing]) >>
      rpt strip_tac >>
      qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) _ _ = _` mp_tac >>
      simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> metis_tac[aux_trace_rules])
  >- (rpt strip_tac >> gvs[Once generate_fn_plan_aux_def] >>
      simp[succ_trace_nil])
  >> rpt gen_tac >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once (cj 4 generate_fn_plan_aux_def), AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[aux_trace_rules]
QED

Theorem dfs_trace_visited_mono:
  (!wl visited ps result tr.
    aux_trace lv dfg cfg fn wl visited ps result tr ==>
    !lbl. MEM lbl visited ==> MEM lbl (FST (SND result))) /\
  (!ss sp succs visited pg result tr.
    succ_trace lv dfg cfg fn ss sp succs visited pg result tr ==>
    !lbl. MEM lbl visited ==> MEM lbl (FST (SND result)))
Proof
  ho_match_mp_tac aux_trace_ind >> rpt conj_tac >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM]
QED

Theorem dfs_trace_label_support:
  (!wl visited ps result tr.
    aux_trace lv dfg cfg fn wl visited ps result tr ==>
    (!lbl. MEM lbl visited ==> MEM lbl (FST (SND result))) /\
    (!lbl p. MEM (lbl,p) tr ==>
      MEM lbl (FST (SND result)) /\ ~MEM lbl visited)) /\
  (!ss sp succs visited pg result tr.
    succ_trace lv dfg cfg fn ss sp succs visited pg result tr ==>
    (!lbl. MEM lbl visited ==> MEM lbl (FST (SND result))) /\
    (!lbl p. MEM (lbl,p) tr ==>
      MEM lbl (FST (SND result)) /\ ~MEM lbl visited))
Proof
  ho_match_mp_tac aux_trace_ind >> rpt conj_tac >>
  rpt strip_tac >> gvs[MEM_APPEND] >> metis_tac[MEM]
QED

Theorem dfs_trace_labels_distinct:
  (!wl visited ps result tr.
    aux_trace lv dfg cfg fn wl visited ps result tr ==>
    ALL_DISTINCT (MAP FST tr)) /\
  (!ss sp succs visited pg result tr.
    succ_trace lv dfg cfg fn ss sp succs visited pg result tr ==>
    ALL_DISTINCT (MAP FST tr))
Proof
  ho_match_mp_tac aux_trace_strongind >> rpt conj_tac >>
  rpt strip_tac >> imp_res_tac dfs_trace_label_support >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP, MEM_APPEND] >>
  metis_tac[PAIR, FST]
QED

Theorem dfs_trace_label_functional:
  (!wl visited ps result tr.
    aux_trace lv dfg cfg fn wl visited ps result tr ==>
    !lbl p q. MEM (lbl,p) tr /\ MEM (lbl,q) tr ==> p = q) /\
  (!ss sp succs visited pg result tr.
    succ_trace lv dfg cfg fn ss sp succs visited pg result tr ==>
    !lbl p q. MEM (lbl,p) tr /\ MEM (lbl,q) tr ==> p = q)
Proof
  `!xs : (string # plan_state) list. ALL_DISTINCT (MAP FST xs) ==>
    !lbl p q. MEM (lbl,p) xs /\ MEM (lbl,q) xs ==> p = q` by
    (Induct >> simp[MEM_MAP] >> rpt strip_tac >>
     gvs[] >> metis_tac[FST, PAIR_EQ]) >>
  rpt strip_tac >> imp_res_tac dfs_trace_labels_distinct >>
  metis_tac[]
QED

Theorem dfs_call_trace_embedding:
  fn_entry_label fn = SOME entry /\
  aux_trace lv dfg cfg fn [entry] [] ps0 root_result root_tr ==>
  ((!wl visited ps.
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    ?result tr. aux_trace lv dfg cfg fn wl visited ps result tr /\
      set tr SUBSET set root_tr) /\
   (!ss sp succs visited pg.
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
    ?result tr. succ_trace lv dfg cfg fn ss sp succs visited pg result tr /\
      set tr SUBSET set root_tr))
Proof
  strip_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[SUBSET_REFL])
  >- (rpt strip_tac >> gvs[aux_trace_visited] >> metis_tac[])
  >- (rpt strip_tac >> gvs[aux_trace_missing] >> metis_tac[])
  >- (rpt strip_tac >> drule_all aux_trace_block >>
      strip_tac >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >> drule_all aux_trace_block >>
      strip_tac >> gvs[] >> imp_res_tac dfs_trace_erasure >>
      gvs[] >> metis_tac[])
  >- (rpt strip_tac >> gvs[succ_trace_cons] >>
      metis_tac[SUBSET_DEF, MEM_APPEND])
  >> rpt strip_tac >> gvs[succ_trace_cons] >>
  imp_res_tac dfs_trace_erasure >> gvs[] >>
  metis_tac[SUBSET_DEF, MEM_APPEND]
QED

Theorem dfs_block_state_trace_mem:
  fn_entry_label fn = SOME entry /\
  aux_trace lv dfg cfg fn [entry] [] ps0 root_result root_tr /\
  dfs_block_state lv dfg cfg fn ps0 lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  MEM (lbl,ps) root_tr
Proof
  rpt strip_tac >> drule_all dfs_call_trace_embedding >> strip_tac >>
  gvs[dfs_block_state_def] >>
  first_x_assum drule >> strip_tac >>
  drule_all aux_trace_block_mem >>
  fs[SUBSET_DEF]
QED
