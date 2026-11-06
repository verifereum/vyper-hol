Theory fnPlanLineageCallTrace
Ancestors stackPlanGen stackPlanOps list

(* Successful evaluation certificates record precisely the fresh aux heads,
   including labels for which block lookup fails. *)
Inductive plan_aux_trace:
  (!lv dfg cfg fn visited ps.
    plan_aux_trace lv dfg cfg fn [] visited ps ([],visited,ps) []) /\
  (!lv dfg cfg fn lbl rest visited ps result events.
    MEM lbl visited /\
    plan_aux_trace lv dfg cfg fn rest visited ps result events ==>
    plan_aux_trace lv dfg cfg fn (lbl::rest) visited ps result events) /\
  (!lv dfg cfg fn lbl rest visited ps result events.
    ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = NONE /\
    plan_aux_trace lv dfg cfg fn rest (lbl::visited) ps result events ==>
    plan_aux_trace lv dfg cfg fn (lbl::rest) visited ps result ((lbl,ps)::events)) /\
  (!lv dfg cfg fn lbl rest visited ps bb block_ops ps1 succ_ops visited1 ps2
      rest_ops visited2 ps3 succ_events rest_events.
    ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb ps = SOME (block_ops,ps1) /\
    plan_succs_trace lv dfg cfg fn ps1.ps_stack ps1.ps_spilled
      (cfg_succs_of cfg lbl) (lbl::visited) ps1 (succ_ops,visited1,ps2) succ_events /\
    plan_aux_trace lv dfg cfg fn rest visited1 ps2 (rest_ops,visited2,ps3) rest_events ==>
    plan_aux_trace lv dfg cfg fn (lbl::rest) visited ps
      (block_ops ++ succ_ops ++ rest_ops,visited2,ps3)
      ((lbl,ps)::(succ_events ++ rest_events))) /\
  (!lv dfg cfg fn stack spilled visited ps.
    plan_succs_trace lv dfg cfg fn stack spilled [] visited ps ([],visited,ps) []) /\
  (!lv dfg cfg fn stack spilled succ rest visited ps ops1 visited1 ps1
      ops2 visited2 ps2 events1 events2.
    plan_aux_trace lv dfg cfg fn [succ] visited
      (ps with <|ps_stack := stack; ps_spilled := spilled|>)
      (ops1,visited1,ps1) events1 /\
    plan_succs_trace lv dfg cfg fn stack spilled rest visited1
      (ps with <|ps_alloc := ps1.ps_alloc with sa_free_slots := ps.ps_alloc.sa_free_slots;
                 ps_label_counter := ps1.ps_label_counter|>)
      (ops2,visited2,ps2) events2 ==>
    plan_succs_trace lv dfg cfg fn stack spilled (succ::rest) visited ps
      (ops1 ++ ops2,visited2,ps2) (events1 ++ events2))
End

Theorem plan_trace_erasure:
  (!lv dfg cfg fn labels visited ps result events.
    plan_aux_trace lv dfg cfg fn labels visited ps result events ==>
    generate_fn_plan_aux lv dfg cfg fn labels visited ps = SOME result) /\
  (!lv dfg cfg fn stack spilled labels visited ps result events.
    plan_succs_trace lv dfg cfg fn stack spilled labels visited ps result events ==>
    generate_succs_plan lv dfg cfg fn stack spilled labels visited ps = SOME result)
Proof
  ho_match_mp_tac plan_aux_trace_ind >> rpt strip_tac >>
  simp[Once generate_fn_plan_aux_def]
QED

Theorem plan_trace_complete:
  (!lv dfg cfg fn labels visited ps.
    !result. generate_fn_plan_aux lv dfg cfg fn labels visited ps = SOME result ==>
    ?events. plan_aux_trace lv dfg cfg fn labels visited ps result events) /\
  (!lv dfg cfg fn stack spilled labels visited ps.
    !result. generate_succs_plan lv dfg cfg fn stack spilled labels visited ps = SOME result ==>
    ?events. plan_succs_trace lv dfg cfg fn stack spilled labels visited ps result events)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (simp[Once generate_fn_plan_aux_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `[]` >> irule (cj 1 plan_aux_trace_rules))
  >- (rpt strip_tac >>
      qpat_x_assum `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME _` mp_tac >>
      simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >>
      gvs[]
      >- (qexists_tac `events` >> irule (cj 2 plan_aux_trace_rules) >> simp[])
      >- (qexists_tac `(lbl,ps)::events` >> irule (cj 3 plan_aux_trace_rules) >> simp[]) >>
      qexists_tac `(lbl,ps)::(events' ++ events)` >>
      irule (cj 4 plan_aux_trace_rules) >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[])
  >- (simp[Once generate_fn_plan_aux_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `[]` >> irule (cj 5 plan_aux_trace_rules)) >>
  rpt strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> qexists_tac `events' ++ events` >>
  irule (cj 6 plan_aux_trace_rules) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem plan_aux_trace_fresh_event:
  plan_aux_trace lv dfg cfg fn (lbl::rest) visited ps result events /\
  ~MEM lbl visited ==> MEM (lbl,ps) events
Proof
  simp[Once plan_aux_trace_cases] >> rpt strip_tac >> gvs[]
QED

Theorem plan_aux_trace_visited_head:
  plan_aux_trace lv dfg cfg fn (lbl::rest) visited ps result events /\
  MEM lbl visited ==>
  plan_aux_trace lv dfg cfg fn rest visited ps result events
Proof
  simp[Once plan_aux_trace_cases] >> rpt strip_tac >> gvs[]
QED

Theorem plan_aux_trace_missing_head:
  plan_aux_trace lv dfg cfg fn (lbl::rest) visited ps result events /\
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = NONE ==>
  ?tail_events. events = (lbl,ps)::tail_events /\
    plan_aux_trace lv dfg cfg fn rest (lbl::visited) ps result tail_events /\
    set tail_events SUBSET set events
Proof
  simp[Once plan_aux_trace_cases] >> rpt strip_tac >> gvs[] >>
  simp[pred_setTheory.SUBSET_DEF]
QED

Theorem plan_aux_trace_present_head:
  plan_aux_trace lv dfg cfg fn (lbl::rest) visited ps result events /\
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (block_ops,ps1) ==>
  ?succ_ops visited1 ps2 rest_ops visited2 ps3 succ_events rest_events.
    result = (block_ops ++ succ_ops ++ rest_ops,visited2,ps3) /\
    events = (lbl,ps)::(succ_events ++ rest_events) /\
    plan_succs_trace lv dfg cfg fn ps1.ps_stack ps1.ps_spilled
      (cfg_succs_of cfg lbl) (lbl::visited) ps1 (succ_ops,visited1,ps2) succ_events /\
    plan_aux_trace lv dfg cfg fn rest visited1 ps2 (rest_ops,visited2,ps3) rest_events /\
    set succ_events SUBSET set events /\ set rest_events SUBSET set events
Proof
  simp[Once plan_aux_trace_cases] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[pred_setTheory.SUBSET_DEF]
QED

Theorem plan_succs_trace_cons:
  plan_succs_trace lv dfg cfg fn stack spilled (succ::rest) visited ps result events ==>
  ?ops1 visited1 ps1 ops2 visited2 ps2 events1 events2.
    result = (ops1 ++ ops2,visited2,ps2) /\ events = events1 ++ events2 /\
    plan_aux_trace lv dfg cfg fn [succ] visited
      (ps with <|ps_stack := stack; ps_spilled := spilled|>)
      (ops1,visited1,ps1) events1 /\
    plan_succs_trace lv dfg cfg fn stack spilled rest visited1
      (ps with <|ps_alloc := ps1.ps_alloc with sa_free_slots := ps.ps_alloc.sa_free_slots;
                 ps_label_counter := ps1.ps_label_counter|>)
      (ops2,visited2,ps2) events2 /\
    set events1 SUBSET set events /\ set events2 SUBSET set events
Proof
  simp[Once plan_aux_trace_cases] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[pred_setTheory.SUBSET_DEF]
QED
