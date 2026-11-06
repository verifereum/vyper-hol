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
