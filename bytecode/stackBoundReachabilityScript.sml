(* Closed checker invariants follow a frame through active and suspended
   intervals.  Runtime transfer laws are parameters, not dependencies. *)
Theory stackBoundReachability
Ancestors
  stackBoundInterface stackBoundDefs frameGas vfmWfState relation

Theorem sb_closed_step[local]:
  sb_step_simulates /\ sb_deeper_preserved /\
  (!q q'. C q /\ MEM q' (sb_successors code q) ==> C q') /\
  wf_state s /\
  (d <= LENGTH s.contexts ==> ?q. C q /\ sb_at code q d s) /\
  d <= LENGTH s.contexts /\ step s = (INL (),t) ==>
  wf_state t /\
  (d <= LENGTH t.contexts ==> ?q. C q /\ sb_at code q d t)
Proof
  rpt strip_tac
  >- (drule step_preserves_wf_state >> simp[]) >>
  `?q. C q /\ sb_at code q d s` by metis_tac[] >>
  Cases_on `d = LENGTH s.contexts`
  >- (PairCases_on `q` >>
      Cases_on `s.contexts` >>
      gvs[sb_at_def] >>
      qpat_x_assum `sb_step_simulates` mp_tac >>
      simp[sb_step_simulates_def] >>
      disch_then (qspecl_then [`s`, `q1`, `t`] mp_tac) >>
      simp[] >> strip_tac >> metis_tac[]) >>
  `d < LENGTH s.contexts` by decide_tac >>
  qexists `q` >>
  metis_tac[sb_deeper_preserved_def]
QED

Theorem sb_frame_inst_invariant:
  sb_step_simulates /\ sb_deeper_preserved /\
  (!q q'. C q /\ MEM q' (sb_successors code q) ==> C q') /\
  C (0,[]) /\ wf_state es /\ es.contexts <> [] /\
  (FST (HD es.contexts)).msgParams.code = code /\
  (FST (HD es.contexts)).pc = 0 /\
  (FST (HD es.contexts)).stack = [] /\
  (FST (HD es.contexts)).jumpDest = NONE /\
  frame_inst_at es s op ==>
  wf_state s /\ sb_decoded (FST (HD s.contexts)) op /\
  ?q. C q /\ sb_at code q (LENGTH es.contexts) s
Proof
  strip_tac >>
  `sb_at code (0,[]) (LENGTH es.contexts) es` by
    (Cases_on `es.contexts` >>
     gvs[sb_at_def, bytecode_stack_describes_def]) >>
  qabbrev_tac `P = \x. wf_state x /\
    (LENGTH es.contexts <= LENGTH x.contexts ==>
     ?q. C q /\ sb_at code q (LENGTH es.contexts) x)` >>
  qabbrev_tac `R = \x y. LENGTH x.contexts >= LENGTH es.contexts /\
    step x = (INL (),y)` >>
  `!x y. P x /\ R x y ==> P y` by
    (simp[Abbr `P`, Abbr `R`] >> rpt gen_tac >> strip_tac >>
     irule sb_closed_step >> simp[] >>
     conj_tac >- metis_tac[] >> qexists `x` >> simp[]) >>
  drule RTC_lifts_invariants >> strip_tac >>
  `P es` by (simp[Abbr `P`] >> metis_tac[]) >>
  qpat_x_assum `frame_inst_at es s op` mp_tac >>
  simp[frame_inst_at_step] >> strip_tac >>
  `P s` by metis_tac[] >>
  gvs[Abbr `P`, Abbr `R`, sb_decoded_def] >> metis_tac[]
QED
