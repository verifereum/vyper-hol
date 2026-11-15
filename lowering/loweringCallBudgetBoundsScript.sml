(* Actual recorded allocation charges, conditional on recorder invariants. *)
Theory loweringCallBudgetBounds
Ancestors
  loweringCallBudgetHistory dallocaBounds calleeTransport venomExecProofs
  words arithmetic list rich_list pred_set combinatorics

Theorem lower_budget_history_charge_from_bounds:
  lower_history_pairs h pair /\ lower_history_current h pair q /\
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) /\
       pair a < LENGTH h ==> charge a <= 2 ** 64) /\
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
       charge a <= 2 ** 255 + 2 ** 64) ==>
  SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
    (GENLIST I (LENGTH h)))) <=
    lower_history_count h * 2 ** 64 + (2 ** 255 + 2 ** 64) /\
  (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
    SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
      (GENLIST I (LENGTH h)))) <= lower_history_count h * 2 ** 64)
Proof
  strip_tac >>
  drule_all lower_budget_completed_pairs_count >> strip_tac >>
  qabbrev_tac `allocs = FILTER (\a. lower_event_allocates (EL a h))
    (GENLIST I (LENGTH h))` >>
  qabbrev_tac `done = FILTER (\a. pair a < LENGTH h) allocs` >>
  qabbrev_tac `pending = FILTER (\a. ~(pair a < LENGTH h)) allocs` >>
  `LENGTH done <= lower_history_count h` by
    (gvs[Abbr `done`, Abbr `allocs`, FILTER_FILTER, CONJ_COMM]) >>
  `SUM (MAP charge done) <= LENGTH done * 2 ** 64` by
    (once_rewrite_tac[MULT_COMM] >> rewrite_tac[GSYM SUM_MAP_K] >>
     irule SUM_MAP_LE >>
     simp[EVERY_MEM, Abbr `done`, Abbr `allocs`, MEM_FILTER, MEM_GENLIST] >>
     gvs[]) >>
  `SUM (MAP charge done) <= lower_history_count h * 2 ** 64` by
    (irule LESS_EQ_TRANS >> goal_assum (drule_at Any) >>
     simp[]) >>
  `SUM (MAP charge allocs) =
    SUM (MAP charge done) + SUM (MAP charge pending)` by
    (simp[Abbr `done`, Abbr `pending`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Induct_on `allocs` >> simp[] >>
     rpt strip_tac >> IF_CASES_TAC >> simp[] >> decide_tac) >>
  conj_tac
  >- (`ALL_DISTINCT pending` by
        simp[Abbr `pending`, Abbr `allocs`, FILTER_ALL_DISTINCT,
             ALL_DISTINCT_GENLIST] >>
      `!a b. MEM a pending /\ MEM b pending ==> a = b` by
        (simp[Abbr `pending`, Abbr `allocs`, MEM_FILTER, MEM_GENLIST] >>
         qpat_x_assum `lower_history_pairs h pair` mp_tac >>
         pure_rewrite_tac[lower_history_pairs_def] >>
         disch_then (CONJUNCTS_THEN2 assume_tac
           (CONJUNCTS_THEN2 kall_tac
             (CONJUNCTS_THEN2 assume_tac kall_tac))) >>
         metis_tac[]) >>
      `SUM (MAP charge pending) <= 2 ** 255 + 2 ** 64` by
        (Cases_on `pending` >- simp[] >>
         rename1 `x::xs` >>
         `xs = []` by
           (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
            qpat_x_assum `!a b. _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            Cases_on `xs` >> simp[] >> metis_tac[MEM]) >>
         qpat_x_assum `xs = []` SUBST_ALL_TAC >>
         `MEM x allocs` by
           (qpat_x_assum `Abbrev (_ = FILTER _ allocs)` mp_tac >>
            simp[markerTheory.Abbrev_def] >> metis_tac[MEM_FILTER, MEM]) >>
         qpat_x_assum `MEM x allocs` mp_tac >>
         simp[Abbr `allocs`, MEM_FILTER, MEM_GENLIST] >>
         fs[] >> metis_tac[]) >>
      decide_tac) >>
  rpt strip_tac >>
  `done = allocs` by
    (simp[Abbr `done`, FILTER_EQ_ID, EVERY_MEM, Abbr `allocs`,
          MEM_FILTER, MEM_GENLIST] >>
     fs[lower_history_current_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem lower_budget_completed_allocation_charge_bound:
  lower_budget_path checked (D,lo,explicit,ctx) root h marks q /\
  root.bp_stack = [] /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  lower_history_pairs h pair /\
  lower_alloc_record h a fn ai pre op sz post /\
  pair a < LENGTH h ==>
  ceil32 (w2n sz) <= 2 ** 64
Proof
  FAIL_TAC "Pending allocation charge proof"
QED

Theorem lower_budget_history_allocation_charge_bound:
  lower_budget_path checked (D,lo,explicit,ctx) root h marks q /\
  root.bp_stack = [] /\
  LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
  lower_history_pairs h pair /\ lower_history_current h pair q /\
  (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ?fn ai pre op sz post.
      lower_alloc_record h a fn ai pre op sz post /\
      charge a = ceil32 (w2n sz)) ==>
  SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
    (GENLIST I (LENGTH h)))) <=
      lower_history_count h * 2 ** 64 + (2 ** 255 + 2 ** 64) /\
  (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
    SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
      (GENLIST I (LENGTH h)))) <= lower_history_count h * 2 ** 64) /\
  (!initial. initial < 2 ** 254 /\ lower_history_count h <= 2 ** 64 ==>
    initial + SUM (MAP charge
      (FILTER (\a. lower_event_allocates (EL a h))
        (GENLIST I (LENGTH h)))) < dimword (:256))
Proof
  FAIL_TAC "Pending allocation charge proof"
QED

