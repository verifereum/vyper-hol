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

Theorem plan_trace_key_invariant[local]:
  (!lv dfg cfg fn labels visited ps result events.
    plan_aux_trace lv dfg cfg fn labels visited ps result events ==>
    set visited SUBSET set (FST (SND result)) /\
    DISJOINT (set (MAP FST events)) (set visited) /\
    set (MAP FST events) SUBSET set (FST (SND result)) /\
    ALL_DISTINCT (MAP FST events)) /\
  (!lv dfg cfg fn stack spilled labels visited ps result events.
    plan_succs_trace lv dfg cfg fn stack spilled labels visited ps result events ==>
    set visited SUBSET set (FST (SND result)) /\
    DISJOINT (set (MAP FST events)) (set visited) /\
    set (MAP FST events) SUBSET set (FST (SND result)) /\
    ALL_DISTINCT (MAP FST events))
Proof
  ho_match_mp_tac plan_aux_trace_ind >> rpt strip_tac >>
  gvs[MAP_APPEND, ALL_DISTINCT_APPEND, pred_setTheory.DISJOINT_DEF,
      pred_setTheory.SUBSET_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem plan_aux_trace_initial_exclusion:
  plan_aux_trace lv dfg cfg fn labels visited ps result events ==>
  DISJOINT (set (MAP FST events)) (set visited)
Proof
  metis_tac[cj 1 plan_trace_key_invariant]
QED

Theorem plan_succs_trace_initial_exclusion:
  plan_succs_trace lv dfg cfg fn stack spilled labels visited ps result events ==>
  DISJOINT (set (MAP FST events)) (set visited)
Proof
  metis_tac[cj 2 plan_trace_key_invariant]
QED

Theorem plan_aux_trace_final_inclusion:
  plan_aux_trace lv dfg cfg fn labels visited ps (ops,visited',out) events ==>
  set (MAP FST events) SUBSET set visited'
Proof
  metis_tac[cj 1 plan_trace_key_invariant, pairTheory.FST, pairTheory.SND]
QED

Theorem plan_succs_trace_final_inclusion:
  plan_succs_trace lv dfg cfg fn stack spilled labels visited ps (ops,visited',out) events ==>
  set (MAP FST events) SUBSET set visited'
Proof
  metis_tac[cj 2 plan_trace_key_invariant, pairTheory.FST, pairTheory.SND]
QED

Theorem plan_aux_trace_distinct_keys:
  plan_aux_trace lv dfg cfg fn labels visited ps result events ==>
  ALL_DISTINCT (MAP FST events)
Proof
  metis_tac[cj 1 plan_trace_key_invariant]
QED

Theorem plan_succs_trace_distinct_keys:
  plan_succs_trace lv dfg cfg fn stack spilled labels visited ps result events ==>
  ALL_DISTINCT (MAP FST events)
Proof
  metis_tac[cj 2 plan_trace_key_invariant]
QED

Theorem distinct_event_keys_unique[local]:
  !events lbl ps qs.
  ALL_DISTINCT (MAP FST events) /\ MEM (lbl,ps) events /\ MEM (lbl,qs) events ==>
  ps = qs
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[MEM_MAP] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem plan_aux_trace_event_unique:
  plan_aux_trace lv dfg cfg fn labels visited ps0 result events /\
  MEM (lbl,ps) events /\ MEM (lbl,qs) events ==> ps = qs
Proof
  metis_tac[plan_aux_trace_distinct_keys, distinct_event_keys_unique]
QED

Theorem plan_succs_trace_event_unique:
  plan_succs_trace lv dfg cfg fn stack spilled labels visited ps0 result events /\
  MEM (lbl,ps) events /\ MEM (lbl,qs) events ==> ps = qs
Proof
  metis_tac[plan_succs_trace_distinct_keys, distinct_event_keys_unique]
QED

Theorem plan_trace_physical_ancestry:
  (!lv dfg cfg fn labels visited ps result events.
    plan_aux_trace lv dfg cfg fn labels visited ps result events ==>
    !pre lbl qs post. LENGTH labels <= 1 /\ events = pre ++ (lbl,qs)::post ==>
      (MEM lbl labels /\ pre = [] /\ qs = ps) \/
      ?pred before bb ops after.
        MEM (pred,before) pre /\ lookup_block pred fn.fn_blocks = SOME bb /\
        generate_block_plan lv dfg cfg fn bb before = SOME (ops,after) /\
        MEM lbl (cfg_succs_of cfg pred) /\
        qs.ps_stack = after.ps_stack /\ qs.ps_spilled = after.ps_spilled) /\
  (!lv dfg cfg fn stack spilled labels visited ps result events.
    plan_succs_trace lv dfg cfg fn stack spilled labels visited ps result events ==>
    !pre lbl qs post. events = pre ++ (lbl,qs)::post ==>
      (MEM lbl labels /\ qs.ps_stack = stack /\ qs.ps_spilled = spilled) \/
      ?pred before bb ops after.
        MEM (pred,before) pre /\ lookup_block pred fn.fn_blocks = SOME bb /\
        generate_block_plan lv dfg cfg fn bb before = SOME (ops,after) /\
        MEM lbl (cfg_succs_of cfg pred) /\
        qs.ps_stack = after.ps_stack /\ qs.ps_spilled = after.ps_spilled)
Proof
  ho_match_mp_tac plan_aux_trace_strongind >> rpt conj_tac
  >- (simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `labels` >> gvs[Once plan_aux_trace_cases])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `labels` >> gvs[Once plan_aux_trace_cases] >>
      Cases_on `pre` >> gvs[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `labels` >> gvs[] >>
      qpat_x_assum `plan_aux_trace _ _ _ _ [] _ _ _ _` mp_tac >>
      simp[Once plan_aux_trace_cases] >> strip_tac >> gvs[] >>
      Cases_on `pre` >> gvs[] >>
      qpat_x_assum `!pre lbl qs post. _` (qspecl_then [`t`, `lbl'`, `qs`, `post`] mp_tac) >>
      simp[] >> metis_tac[])
  >- simp[]
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `pre ++ [(lbl,qs)] ++ post = events ++ events'` by simp[] >>
  pop_assum mp_tac >> simp_tac bool_ss [APPEND_EQ_APPEND_MID] >>
  strip_tac >> gvs[]
  >- (qpat_x_assum `!p x q s. pre ++ [(lbl,qs)] ++ l = _ ==> _`
        (qspecl_then [`pre`, `lbl`, `qs`, `l`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `!pre lbl qs post. _` (qspecl_then [`l`, `lbl`, `qs`, `post`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[MEM_APPEND]
QED

Theorem plan_aux_trace_singleton_physical_ancestry:
  plan_aux_trace lv dfg cfg fn [root] visited ps result events /\
  events = pre ++ (lbl,qs)::post ==>
  (lbl = root /\ pre = [] /\ qs = ps) \/
  ?pred before bb ops after.
    MEM (pred,before) pre /\ lookup_block pred fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb before = SOME (ops,after) /\
    MEM lbl (cfg_succs_of cfg pred) /\
    qs.ps_stack = after.ps_stack /\ qs.ps_spilled = after.ps_spilled
Proof
  strip_tac >> drule (cj 1 plan_trace_physical_ancestry) >>
  disch_then (qspecl_then [`pre`, `lbl`, `qs`, `post`] mp_tac) >> simp[]
QED

Theorem plan_succs_trace_physical_ancestry:
  plan_succs_trace lv dfg cfg fn stack spilled labels visited ps result events /\
  events = pre ++ (lbl,qs)::post ==>
  (MEM lbl labels /\ qs.ps_stack = stack /\ qs.ps_spilled = spilled) \/
  ?pred before bb ops after.
    MEM (pred,before) pre /\ lookup_block pred fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb before = SOME (ops,after) /\
    MEM lbl (cfg_succs_of cfg pred) /\
    qs.ps_stack = after.ps_stack /\ qs.ps_spilled = after.ps_spilled
Proof
  strip_tac >> drule (cj 2 plan_trace_physical_ancestry) >>
  disch_then (qspecl_then [`pre`, `lbl`, `qs`, `post`] mp_tac) >> simp[]
QED

(* Exact copy from vyperTypeCallGraphSoundnessTheory: importing that
   semantics theory here would cross the planner-leaf boundary. *)
Theorem LRC_APPEND:
  LRC R (l1 ++ l2) x z <=> ?y. LRC R l1 x y /\ LRC R l2 y z
Proof
  qid_spec_tac `x` >> Induct_on `l1` >> simp[listTheory.LRC_def] >> metis_tac[]
QED

Theorem LRC_first_hit:
  !ls x y. LRC R ls x y /\ (EXISTS P ls \/ P y) ==>
    ?pre hit post. ls = pre ++ post /\
      LRC R pre x hit /\ LRC R post hit y /\
      P hit /\ EVERY (\v. ~P v) pre
Proof
  Induct >- (simp[listTheory.LRC_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
  simp[Once listTheory.LRC_def] >> strip_tac >> gnvs[] >>
  Cases_on `P h`
  >- (qexistsl_tac [`[]`,`h`,`h::ls`] >> simp[listTheory.LRC_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`z`,`y`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qexistsl_tac [`h::pre`,`hit`,`post`] >> simp[listTheory.LRC_def] >> metis_tac[]
QED

Theorem LRC_consecutive_return:
  LRC R pre root a /\ R a z /\ LRC R rest z final /\
  P a /\ (EXISTS P rest \/ P final) ==>
  ?middle b post.
    rest = middle ++ post /\ P b /\ EVERY (\v. ~P v) middle /\
    LRC R pre root a /\ LRC R (a::middle) a b /\ LRC R post b final /\
    LRC R (pre ++ a::rest) root final
Proof
  strip_tac >> drule LRC_first_hit >>
  disch_then (qspec_then `P` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`pre'`,`hit`,`post`] >>
  simp[LRC_APPEND, listTheory.LRC_def] >> metis_tac[]
QED
