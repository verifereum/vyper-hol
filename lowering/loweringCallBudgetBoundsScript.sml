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

(* Successful recorded steps retain the root call context, including across
   suspended caller frames and return-value binding. *)
Theorem lower_budget_path_charge_facts:
  lower_budget_path checked (D,lo,explicit,ctx) root h marks q /\
  root.bp_stack = [] ==>
  q.bp_state.vs_call_ctx = root.bp_state.vs_call_ctx /\
  (!f. MEM f q.bp_stack ==>
    f.cf_state.vs_call_ctx = root.bp_state.vs_call_ctx) /\
  (!n p i fuel t r.
    n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) r ==>
    step_inst fuel ctx i p.bp_state = OK t /\
    p.bp_state.vs_call_ctx = root.bp_state.vs_call_ctx)
Proof
  qsuff_tac
    `!checked cfg root h marks q.
      lower_budget_path checked cfg root h marks q ==>
      !D lo explicit ctx. cfg = (D,lo,explicit,ctx) /\
      root.bp_stack = [] ==>
      q.bp_state.vs_call_ctx = root.bp_state.vs_call_ctx /\
      (!f. MEM f q.bp_stack ==>
        f.cf_state.vs_call_ctx = root.bp_state.vs_call_ctx) /\
      (!n p i fuel t r.
        n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) r ==>
        step_inst fuel ctx i p.bp_state = OK t /\
        p.bp_state.vs_call_ctx = root.bp_state.vs_call_ctx)`
  >- metis_tac[] >>
  ho_match_mp_tac lower_budget_path_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (conj_tac
      >- metis_tac[step_inst_ok_preserves_call_ctx] >>
      rpt gen_tac >> strip_tac >>
      Cases_on `n < LENGTH h`
      >- (gvs[EL_APPEND_EQN] >> metis_tac[]) >>
      `n = LENGTH h` by decide_tac >>
      gvs[EL_APPEND_EQN])
  >- (conj_tac
      >- (gvs[contextCodegenRelTheory.enters_block_def] >>
          drule eval_phis_only_updates_vs_vars >> strip_tac >>
          qpat_x_assum `s_phi = _` (fn th => once_rewrite_tac[th]) >>
          simp[] >> metis_tac[step_inst_ok_preserves_call_ctx]) >>
      rpt gen_tac >> strip_tac >>
      Cases_on `n < LENGTH h`
      >- (gvs[EL_APPEND_EQN] >> metis_tac[]) >>
      `n = LENGTH h` by decide_tac >>
      gvs[EL_APPEND_EQN])
  >- (conj_tac
      >- (drule setup_callee_shared_fields >> strip_tac >>
          gvs[contextCodegenRelTheory.enters_block_def] >>
          drule eval_phis_only_updates_vs_vars >> strip_tac >>
          qpat_x_assum `s_phi = _` (fn th => once_rewrite_tac[th]) >>
          simp[]) >>
      conj_tac >- (rpt strip_tac >> gvs[]) >>
      rpt gen_tac >> strip_tac >> Cases_on `n < LENGTH h`
      >- (gvs[EL_APPEND_EQN] >> metis_tac[]) >>
      `n = LENGTH h` by decide_tac >> gvs[EL_APPEND_EQN]) >>
  conj_tac
  >- (qspec_then `\s. s.vs_call_ctx` mp_tac
        venomInstProofs1Theory.bind_outputs_preserves >>
      simp[venomStateTheory.update_var_def] >>
      disch_then drule >> strip_tac >>
      `(adopt_return_fmp ret (merge_callee_state f.cf_state s_end)).vs_call_ctx =
       (merge_callee_state f.cf_state s_end).vs_call_ctx` by
        (irule adopt_return_fmp_projection >> simp[]) >>
      gvs[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `n < LENGTH h`
  >- (gvs[EL_APPEND_EQN] >> metis_tac[]) >>
  `n = LENGTH h` by decide_tac >> gvs[EL_APPEND_EQN]
QED

Theorem lower_budget_completed_charge_from_records:
  lower_history_pairs h pair /\
  lower_alloc_record h a fn ai pre op sz post /\
  pair a < LENGTH h /\
  LENGTH pre.vs_call_ctx.cc_calldata < 2 ** 64 /\
  (!n p i fuel t r.
    n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) r ==>
    step_inst fuel ctx i p.bp_state = OK t) ==>
  ceil32 (w2n sz) <= 2 ** 64
Proof
  strip_tac >>
  `a < LENGTH h /\ lower_event_allocates (EL a h)` by
    gvs[lower_alloc_record_def, lower_event_allocates_def] >>
  qpat_x_assum `lower_history_pairs h pair`
    (qspec_then `a` mp_tac o cj 4 o REWRITE_RULE [lower_history_pairs_def]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!j. _ ==> ?jp ji jf jt jq. _` kall_tac >>
  gvs[lower_alloc_record_def] >>
  rename1 `EL a h = BudgetStep a ap ai af (OK post) aq` >>
  rename1 `EL (pair a) h = BudgetStep (pair a) ep ei ef (OK et) eq`
  >>~- ([`ceil32 (_ MOD _) <= _`],
    (`LENGTH ap.bp_state.vs_call_ctx.cc_calldata < dimword (:256)` by
       (simp[dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
     simp[] >>
     qspec_then `ap.bp_state.vs_call_ctx.cc_calldata` mp_tac
       (GEN_ALL dalloca_calldata_size_bound) >>
     simp[contractABITheory.ceil32_def,
          fmpAlignmentTheory.ceil32_div_mul, MULT_COMM])) >>
  `step_inst ef ctx ei ep.bp_state = OK et` by metis_tac[] >>
  `step_inst_base ei ep.bp_state = OK et` by
    (qpat_x_assum `step_inst ef ctx ei ep.bp_state = OK et` mp_tac >>
     simp[Once venomExecSemanticsTheory.step_inst_def]) >>
  `MEM ei.inst_opcode [CREATE; CREATE2]` by simp[] >>
  drule_all lowerDloadSafetyCreateTheory.ld_create_dispatch >>
  strip_tac >>
  gvs[venomStateTheory.eval_operands_def] >>
  drule_then assume_tac dalloca_completed_create_size_bound >>
  drule_then strip_assume_tac dalloca_completed_copy_size_bound >>
  gvs[contractABITheory.ceil32_def,
      fmpAlignmentTheory.ceil32_div_mul, MULT_COMM] >>
  decide_tac
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

