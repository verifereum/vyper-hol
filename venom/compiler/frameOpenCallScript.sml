Theory frameOpenCall
Ancestors frameJointTransition frameJointTrace frameActivationCache
  venomState venomInst arithmetic list

Theorem last_index_in_interval[local]:
  !j (n:num). n <= j /\ P n ==>
  ?c. n <= c /\ c <= j /\ P c /\ (!k. c < k /\ k <= j ==> ~P k)
Proof
  Induct >- (rpt strip_tac >> `n = 0` by decide_tac >> gvs[]) >>
  rpt strip_tac >> Cases_on `P (SUC j)`
  >- (qexists_tac `SUC j` >> simp[] >> rpt strip_tac >> decide_tac) >>
  `n <= j` by (Cases_on `n = SUC j` >> gvs[] >> decide_tac) >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qexists_tac `c` >> simp[] >>
  rpt strip_tac >> Cases_on `k = SUC j` >> gvs[] >>
  first_x_assum irule >> decide_tac
QED

Theorem joint_depth_increase_call[local]:
  joint_transition ctx p ev q /\ activation_depth p < activation_depth q ==>
  ev = NONE
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[activation_depth_def]
QED

Theorem joint_open_call_cut:
  joint_trace vs0 ctx q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  activation_depth (EL n (q0::qs)) = d /\
  d < activation_depth (EL j (q0::qs)) /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) ==>
  ?c. n <= c /\ c < j /\ activation_depth (EL c (q0::qs)) = d /\
    EL c es = NONE /\
    joint_transition ctx (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
    (!k. c < k /\ k <= j ==> d < activation_depth (EL k (q0::qs)))
Proof
  strip_tac >>
  `?c. n <= c /\ c <= j /\ activation_depth (EL c (q0::qs)) = d /\
    (!k. c < k /\ k <= j ==> activation_depth (EL k (q0::qs)) <> d)` by
    (ho_match_mp_tac last_index_in_interval >> simp[]) >>
  `c < j /\ c < LENGTH es /\ SUC c <= j` by
    (Cases_on `c = j` >> gvs[] >> decide_tac) >>
  `!k. c < k /\ k <= j ==> d < activation_depth (EL k (q0::qs))` by
    (rpt strip_tac >>
     `n <= k` by decide_tac >>
     `d <= activation_depth (EL k (q0::qs)) /\
      activation_depth (EL k (q0::qs)) <> d` by metis_tac[] >> decide_tac) >>
  `joint_transition ctx (EL c (q0::qs)) (EL c es) (EL (SUC c) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `EL c es = NONE` by
    (irule joint_depth_increase_call >> goal_assum (drule_at Any) >>
     qpat_x_assum `!k. c < k /\ k <= j ==> d < _`
       (qspec_then `SUC c` mp_tac) >> simp[]) >>
  qexists_tac `c` >> gvs[]
QED

Theorem joint_saved_frame_step[local]:
  joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' s' oms' om' hs' h') /\
  d < LENGTH stk /\ d < LENGTH stk' ==>
  EL (LENGTH stk' - SUC d) stk' = EL (LENGTH stk - SUC d) stk
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[] >>
  rename1 `d < LENGTH tail` >>
  `LENGTH tail - d = SUC (LENGTH tail - SUC d)` by decide_tac >> gvs[]
QED

Theorem joint_saved_frame_interval[local]:
  !j n. joint_trace vs0 ctx q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  EL n (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn0 inst0 s0 oms0 om0 hs0 h0 /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  (!k. n <= k /\ k <= j ==> d < activation_depth (EL k (q0::qs))) ==>
  EL (LENGTH stk - SUC d) stk = EL (LENGTH stk0 - SUC d) stk0
Proof
  map_every qid_spec_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`oms`,`om`,`hs`,`h`] >>
  Induct_on `j` >- (rpt strip_tac >> `n = 0` by decide_tac >> gvs[]) >>
  rpt strip_tac >> Cases_on `n = SUC j` >- gvs[] >>
  `n <= j /\ j < LENGTH es` by decide_tac >>
  Cases_on `EL j (q0::qs)` >>
  rename1 `EL j (q0::qs) = JointConfig stkj PGj Gj tnj fnj instj sj omsj omj hsj hj` >>
  `EL (LENGTH stkj - SUC d) stkj = EL (LENGTH stk0 - SUC d) stk0` by
    (first_x_assum irule >> goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `n` >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `joint_transition ctx (EL j (q0::qs)) (EL j es) (EL (SUC j) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `d < LENGTH stkj /\ d < LENGTH stk` by
    (qpat_assum `!k. _ ==> d < _` (qspec_then `j` mp_tac) >>
     qpat_x_assum `!k. _ ==> d < _` (qspec_then `SUC j` mp_tac) >>
     simp[activation_depth_def]) >>
  `EL (LENGTH stk - SUC d) stk = EL (LENGTH stkj - SUC d) stkj` by
    (qpat_x_assum `EL (LENGTH stkj - SUC d) stkj = _` kall_tac >>
     qpat_x_assum `joint_transition _ _ _ _` mp_tac >> simp[] >> strip_tac >>
     irule joint_saved_frame_step >> simp[] >>
     goal_assum (drule_at (Pat `joint_transition _ _ _ _`))) >>
  metis_tac[]
QED

Theorem joint_open_call_saved_at[local]:
  joint_trace vs0 ctx q0 es qs q /\ c < j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 owner invoke s0 oms0 om0 hs0 h0 /\
  LENGTH stk0 = d /\
  joint_transition ctx (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h /\
  (!k. c < k /\ k <= j ==> d < activation_depth (EL k (q0::qs))) ==>
  (EL (LENGTH stk - SUC d) stk).cf_fn = owner /\
  (EL (LENGTH stk - SUC d) stk).cf_inst = invoke /\
  (EL (LENGTH stk - SUC d) stk).cf_state = s0 /\ invoke.inst_opcode = INVOKE
Proof
  strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_call_iff] >> strip_tac >>
  `SUC c <= j` by decide_tac >>
  qmatch_asmsub_abbrev_tac `JointConfig (saved::stk0) _ _ _ _ _ _ _ _ _ _` >>
  `EL (SUC c) (q0::qs) = JointConfig (saved::stk0)
    (MAP (op_prov G0) ops) FEMPTY (tn0 with t_var := FEMPTY) callee inst' s1
    (om0::oms0) FEMPTY (h0::hs0)
    [OriginCallee cs; OriginObserve
      (OriginSnapshot callee (MAP (op_prov G0) ops) FEMPTY FEMPTY inst' s1)]` by simp[] >>
  `EL (LENGTH stk - SUC d) stk =
    EL (LENGTH (saved::stk0) - SUC d) (saved::stk0)` by
    (irule joint_saved_frame_interval >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = JointConfig stk _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[Abbr `saved`]
QED

Theorem joint_open_call_saved:
  joint_trace vs0 ctx q0 es qs q /\ n <= j /\ j <= LENGTH es /\
  activation_depth (EL n (q0::qs)) = d /\
  d < activation_depth (EL j (q0::qs)) /\
  (!k. n <= k /\ k <= j ==> d <= activation_depth (EL k (q0::qs))) /\
  EL j (q0::qs) = JointConfig stk PG G tn current inst s oms om hs h ==>
  ?c stk0 PG0 G0 tn0 owner invoke s0 oms0 om0 hs0 h0.
    n <= c /\ c < j /\ LENGTH stk0 = d /\ EL c es = NONE /\
    EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 owner invoke s0 oms0 om0 hs0 h0 /\
    joint_transition ctx (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
    (!k. c < k /\ k <= j ==> d < activation_depth (EL k (q0::qs))) /\
    (EL (LENGTH stk - SUC d) stk).cf_fn = owner /\
    (EL (LENGTH stk - SUC d) stk).cf_inst = invoke /\
    (EL (LENGTH stk - SUC d) stk).cf_state = s0 /\ invoke.inst_opcode = INVOKE
Proof
  strip_tac >> drule_all joint_open_call_cut >> strip_tac >>
  Cases_on `EL c (q0::qs)` >>
  rename1 `EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 owner invoke s0 oms0 om0 hs0 h0` >>
  `LENGTH stk0 = d` by gvs[activation_depth_def] >>
  ` (EL (LENGTH stk - SUC d) stk).cf_fn = owner /\
    (EL (LENGTH stk - SUC d) stk).cf_inst = invoke /\
    (EL (LENGTH stk - SUC d) stk).cf_state = s0 /\ invoke.inst_opcode = INVOKE` by
    (irule joint_open_call_saved_at >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >> gvs[]) >>
  qexists_tac `c` >> goal_assum (drule_at (Pat `EL _ _ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >> gvs[]
QED
