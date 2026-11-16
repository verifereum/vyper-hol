(* Actual recorded allocation charges, conditional on recorder invariants. *)
Theory loweringCallBudgetBounds
Ancestors
  loweringCallBudgetHistory dallocaBounds calleeTransport venomExecProofs
  words arithmetic list rich_list pred_set combinatorics
  ptrDisciplineEmptyTaint ctxLookupAgreeHelpers frameAllocationEffects
  ptrSafeRun opcodeClass venomExecSemantics venomState


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
  strip_tac >>
  drule_all lower_budget_path_charge_facts >> strip_tac >>
  `LENGTH pre.vs_call_ctx.cc_calldata < 2 ** 64` by
    (qpat_x_assum `lower_alloc_record h a fn ai pre op sz post` mp_tac >>
     rewrite_tac[lower_alloc_record_def] >> strip_tac >> metis_tac[]) >>
  `!n p i fuel t r.
    n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) r ==>
    step_inst fuel ctx i p.bp_state = OK t` by metis_tac[] >>
  drule_all lower_budget_completed_charge_from_records >> simp[]
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
  strip_tac >>
  `!a. a < LENGTH h /\ lower_event_allocates (EL a h) /\
       pair a < LENGTH h ==> charge a <= 2 ** 64` by
    (rpt strip_tac >>
     qpat_x_assum `!a. _ ==> ?fn ai pre op sz post. _`
       (qspec_then `a` mp_tac) >>
     simp[] >> strip_tac >>
     drule_all lower_budget_completed_allocation_charge_bound >> simp[]) >>
  `!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
       charge a <= 2 ** 255 + 2 ** 64` by
    (rpt strip_tac >>
     qpat_x_assum `!a. _ ==> ?fn ai pre op sz post. _`
       (qspec_then `a` mp_tac) >>
     simp[] >> strip_tac >>
     `w2n sz <= 32 * (2 ** 250 + 2 ** 59)` by
       fs[lower_alloc_record_def] >>
     drule ceil32_le_multiple >>
     simp[contractABITheory.ceil32_def,
          fmpAlignmentTheory.ceil32_div_mul, MULT_COMM]) >>
  drule_all lower_budget_history_charge_from_bounds >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  drule_all dalloca_split_budget >> decide_tac
QED

(* Successful non-call instructions either retain, reclaim, or charge FMP. *)
Theorem lower_budget_step_fmp_interval:
  step_inst fuel ctx i s = OK t /\ i.inst_opcode <> INVOKE /\
  s.vs_initial_fmp = init /\
  L <= w2n s.vs_fmp /\ w2n s.vs_fmp <= U /\
  U + c < dimword (:256) /\
  (i.inst_opcode = SETFMP ==>
    L <= w2n t.vs_fmp /\ w2n t.vs_fmp <= w2n s.vs_fmp) /\
  (i.inst_opcode <> DALLOCA ==> c = 0) /\
  (i.inst_opcode = DALLOCA ==> ?op sz.
    i.inst_operands = [op] /\ eval_operand op s = SOME sz /\
    c = ceil32 (w2n sz)) ==>
  t.vs_initial_fmp = init /\
  L <= w2n t.vs_fmp /\ w2n t.vs_fmp <= U + c
Proof
  strip_tac >>
  `t.vs_initial_fmp = init` by metis_tac[step_inst_initial_fmp] >>
  simp[] >>
  Cases_on `i.inst_opcode = SETFMP` >- (gvs[] >> decide_tac) >>
  Cases_on `i.inst_opcode = DALLOCA`
  >- (gvs[step_inst_non_invoke] >>
      qpat_x_assum `step_inst_base i s = OK t` mp_tac >>
      simp[step_inst_base_opcode_eqs] >>
      strip_tac >> gvs[AllCaseEqs(), update_var_def] >>
      gvs[contractABITheory.ceil32_def,
          fmpAlignmentTheory.ceil32_div_mul, MULT_COMM] >>
      qmatch_goalsub_abbrev_tac `s.vs_fmp + n2w charge` >>
      `w2n s.vs_fmp + charge < dimword (:256)` by
        (simp[Abbr `charge`] >> decide_tac) >>
      drule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >>
      disch_then SUBST1_TAC >> simp[Abbr `charge`]) >>
  `c = 0` by simp[] >> gvs[] >>
  Cases_on `allocation_free_opcode i.inst_opcode`
  >- (drule_all allocation_free_step_fmp_ok >> simp[]) >>
  `i.inst_opcode = ALLOCA \/ i.inst_opcode = RETFMP \/
   i.inst_opcode = DRET` by gvs[allocation_free_opcode_def] >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base i s = OK t` mp_tac >>
  simp[step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()]
  >- (drule exec_alloca_preserves_fmp >> simp[]) >>
  pairarg_tac >> gvs[]
QED

(* RET restores the saved frontier; RETFMP adopts the live callee frontier. *)
Theorem lower_budget_return_fmp_interval:
  step_inst fuel ctx i s = IntRet ret se /\ i.inst_opcode <> DRET /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller se)) = SOME t /\
  caller.vs_initial_fmp = init /\
  L <= w2n caller.vs_fmp /\ w2n caller.vs_fmp <= U /\
  L <= w2n s.vs_fmp /\ w2n s.vs_fmp <= U ==>
  t.vs_initial_fmp = init /\
  L <= w2n t.vs_fmp /\ w2n t.vs_fmp <= U
Proof
  strip_tac >>
  `t.vs_initial_fmp = init` by
    (drule bind_outputs_initial_fmp >> simp[]) >> simp[] >>
  drule bind_outputs_allocation_frame >> strip_tac >>
  `i.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  `step_inst_base i s = IntRet ret se` by gvs[step_inst_non_invoke] >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base i s = IntRet ret se` mp_tac >>
  simp[step_inst_base_opcode_eqs] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem lower_budget_charge_snoc[local]:
  SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a (h ++ [e])))
    (GENLIST I (LENGTH (h ++ [e]))))) =
  SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
    (GENLIST I (LENGTH h)))) +
  (if lower_event_allocates e then charge (LENGTH h) else 0)
Proof
  `FILTER (\a. lower_event_allocates (EL a (h ++ [e])))
     (GENLIST I (LENGTH h)) =
   FILTER (\a. lower_event_allocates (EL a h))
     (GENLIST I (LENGTH h))` by
    (simp[FILTER_EQ, MEM_GENLIST, EL_APPEND_EQN]) >>
  simp[LENGTH_APPEND, GSYM ADD1, GENLIST, SNOC_APPEND, FILTER_APPEND,
       MAP_APPEND, SUM_APPEND] >>
  Cases_on `lower_event_allocates e` >> simp[EL_APPEND_EQN]
QED

Theorem lower_budget_path_fmp_envelope:
  (!fuel ctx i s t I L U c.
    step_inst fuel ctx i s = OK t /\ i.inst_opcode <> INVOKE /\
    s.vs_initial_fmp = I /\ L <= w2n s.vs_fmp /\ w2n s.vs_fmp <= U /\
    U + c < dimword (:256) /\
    (i.inst_opcode = SETFMP ==>
      L <= w2n t.vs_fmp /\ w2n t.vs_fmp <= w2n s.vs_fmp) /\
    (i.inst_opcode <> DALLOCA ==> c = 0) /\
    (i.inst_opcode = DALLOCA ==>
      ?op sz. i.inst_operands = [op] /\ eval_operand op s = SOME sz /\
        c = ceil32 (w2n sz)) ==>
    t.vs_initial_fmp = I /\ L <= w2n t.vs_fmp /\ w2n t.vs_fmp <= U + c) /\
  (!fuel ctx i s ret se caller t I L U.
    step_inst fuel ctx i s = IntRet ret se /\ i.inst_opcode <> DRET /\
    bind_outputs caller.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state caller.cf_state se)) = SOME t /\
    caller.cf_state.vs_initial_fmp = I /\
    L <= w2n caller.cf_state.vs_fmp /\ w2n caller.cf_state.vs_fmp <= U /\
    L <= w2n s.vs_fmp /\ w2n s.vs_fmp <= U ==>
    t.vs_initial_fmp = I /\ L <= w2n t.vs_fmp /\ w2n t.vs_fmp <= U) ==>
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    !charge.
      root.bp_stack = [] /\
      root.bp_state.vs_fmp = root.bp_state.vs_initial_fmp /\
      (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
        ?fn ai pre op sz post.
          lower_alloc_record h a fn ai pre op sz post /\
          charge a = ceil32 (w2n sz)) /\
      (!n p i fuel t r.
        n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) r /\
        i.inst_opcode = SETFMP ==>
        w2n root.bp_state.vs_initial_fmp <= w2n t.vs_fmp /\
        w2n t.vs_fmp <= w2n p.bp_state.vs_fmp) /\
      (!n p i fuel ret se t r.
        n < LENGTH h /\ EL n h = BudgetReturn n p i fuel ret se t r ==>
        i.inst_opcode <> DRET) /\
      w2n root.bp_state.vs_initial_fmp +
        SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
          (GENLIST I (LENGTH h)))) < dimword (:256) ==>
      q.bp_state.vs_initial_fmp = root.bp_state.vs_initial_fmp /\
      w2n root.bp_state.vs_initial_fmp <= w2n q.bp_state.vs_fmp /\
      w2n q.bp_state.vs_fmp <= w2n root.bp_state.vs_initial_fmp +
        SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
          (GENLIST I (LENGTH h)))) /\
      (!f. MEM f q.bp_stack ==>
        f.cf_state.vs_initial_fmp = root.bp_state.vs_initial_fmp /\
        w2n root.bp_state.vs_initial_fmp <= w2n f.cf_state.vs_fmp /\
        w2n f.cf_state.vs_fmp <= w2n root.bp_state.vs_initial_fmp +
          SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
            (GENLIST I (LENGTH h)))))
Proof
  strip_tac >>
  qpat_x_assum `!fuel ctx i s t I L U c.
    step_inst fuel ctx i s = OK t /\ _ ==> _` (mk_asm "step") >>
  qpat_x_assum `!fuel ctx i s ret se caller t I L U.
    step_inst fuel ctx i s = IntRet ret se /\ _ ==> _` (mk_asm "ret") >>
  ho_match_mp_tac lower_budget_path_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac
  >- simp[]
  >> qpat_x_assum `!charge. root.bp_stack = [] /\ _ ==> _` (mk_asm "ih")
  >> gvs[lower_budget_charge_snoc, lower_event_allocates_def]
  >> asm_x "ih" (qspec_then `charge` mp_tac)
  >> (impl_tac >-
    (simp[] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!a. _ ==> ?fn ai pre op sz post. _`
           (qspec_then `a` mp_tac) >>
         simp[lower_alloc_record_def, EL_APPEND_EQN])
     >- (rpt strip_tac >>
         qpat_x_assum `!n p i fuel t r.
           n < _ /\ _ = BudgetStep n p i fuel (OK t) r /\ _ ==> _`
           (qspec_then `n` mp_tac) >>
         simp[EL_APPEND_EQN] >> metis_tac[])
     >- (rpt strip_tac >>
         qpat_x_assum `!n p i fuel ret se t r.
           n < _ /\ _ = BudgetReturn n p i fuel ret se t r ==> _`
           (qspec_then `n` mp_tac) >>
         simp[EL_APPEND_EQN] >> metis_tac[])
     >> qpat_x_assum `_ < dimword (:256)` mp_tac >>
        rpt IF_CASES_TAC >> decide_tac))
  >> strip_tac
  >> qpat_x_assum `!a. _ ==> ?fn ai pre op sz post. _` (mk_asm "alloc")
  >> qpat_x_assum `!n p i fuel t r.
       n < _ /\ _ = BudgetStep n p i fuel (OK t) r /\ _ ==> _` (mk_asm "reclaim")
  >> qpat_x_assum `!n p i fuel ret se t r.
       n < _ /\ _ = BudgetReturn n p i fuel ret se t r ==> _` (mk_asm "noDRET")
  >> qabbrev_tac `spent = SUM (MAP charge
       (FILTER (\a. lower_event_allocates (EL a h)) (GENLIST I (LENGTH h))))`
  >- (asm "step" drule >>
      disch_then (qspecl_then
        [`root.bp_state.vs_initial_fmp`, `w2n root.bp_state.vs_initial_fmp`,
         `w2n root.bp_state.vs_initial_fmp + spent`,
         `if i.inst_opcode = DALLOCA then charge (LENGTH h) else 0`] mp_tac) >>
      (impl_tac >-
        (simp[] >> conj_tac
         >- (asm "reclaim" (qspec_then `LENGTH h` mp_tac) >>
             simp[EL_APPEND_EQN])
         >> strip_tac >>
         asm "alloc" (qspec_then `LENGTH h` mp_tac) >>
         simp[EL_APPEND_EQN, lower_event_allocates_def, lower_alloc_record_def] >>
         metis_tac[])) >>
      strip_tac >> simp[] >> conj_tac >- gvs[] >>
      rpt strip_tac >>
      qpat_x_assum `!f. MEM f q.bp_stack ==> _` drule >>
      strip_tac >> simp[] >> IF_CASES_TAC >> decide_tac)
  >- (`i.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_invoke] >>
      asm "step" drule >>
      disch_then (qspecl_then
        [`root.bp_state.vs_initial_fmp`, `w2n root.bp_state.vs_initial_fmp`,
         `w2n root.bp_state.vs_initial_fmp + spent`,
         `if i.inst_opcode = DALLOCA then charge (LENGTH h) else 0`] mp_tac) >>
      (impl_tac >-
        (simp[] >> conj_tac
         >- (asm "reclaim" (qspec_then `LENGTH h` mp_tac) >>
             simp[EL_APPEND_EQN]) >> strip_tac >>
         asm "alloc" (qspec_then `LENGTH h` mp_tac) >>
         simp[EL_APPEND_EQN, lower_event_allocates_def, lower_alloc_record_def] >>
         metis_tac[])) >> strip_tac >>
      qpat_x_assum `enters_block _ _ _` mp_tac >>
      simp[contextCodegenRelTheory.enters_block_def] >> strip_tac >>
      qpat_x_assum `_ = _ with vs_inst_idx := _` SUBST_ALL_TAC >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => pure_once_rewrite_tac[th]) >>
      simp[] >> conj_tac >- gvs[] >> rpt strip_tac >>
      qpat_x_assum `!f. MEM f q.bp_stack ==> _` drule >>
      strip_tac >> simp[] >> IF_CASES_TAC >> decide_tac)
  >- (drule setup_callee_shared_fields >> strip_tac >>
      drule setup_callee_frame >> strip_tac >>
      qpat_x_assum `enters_block _ _ _` mp_tac >>
      simp[contextCodegenRelTheory.enters_block_def] >> strip_tac >>
      qpat_x_assum `_ = _ with vs_inst_idx := _` SUBST_ALL_TAC >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => pure_once_rewrite_tac[th]) >>
      simp[ADD_COMM] >> rpt strip_tac >> gvs[])
  >> `i.inst_opcode <> DRET` by
       (asm "noDRET" (qspec_then `LENGTH h` mp_tac) >> simp[EL_APPEND_EQN])
  >> `f.cf_state.vs_initial_fmp = root.bp_state.vs_initial_fmp /\
      w2n root.bp_state.vs_initial_fmp <= w2n f.cf_state.vs_fmp /\
      w2n f.cf_state.vs_fmp <= w2n root.bp_state.vs_initial_fmp + spent` by
       (qpat_x_assum `!f. MEM f q.bp_stack ==> _` (qspec_then `f` mp_tac) >> simp[])
  >> asm "ret" drule
  >> disch_then (qspecl_then
       [`f`, `s'`, `root.bp_state.vs_initial_fmp`,
        `w2n root.bp_state.vs_initial_fmp`,
        `w2n root.bp_state.vs_initial_fmp + spent`] mp_tac)
  >> simp[] >> strip_tac >> simp[ADD_COMM] >> rpt strip_tac >>
     qpat_x_assum `!f. MEM f q.bp_stack ==> _` (qspec_then `f'` mp_tac) >>
     simp[ADD_COMM]
QED

Theorem lower_budget_history_fmp_nowrap:
  !checked D lo explicit ctx root h marks q pair.
    lower_budget_path checked (D,lo,explicit,ctx) root h marks q /\
    root.bp_stack = [] /\
    root.bp_state.vs_fmp = root.bp_state.vs_initial_fmp /\
    w2n root.bp_state.vs_initial_fmp < 2 ** 254 /\
    LENGTH root.bp_state.vs_call_ctx.cc_calldata < 2 ** 64 /\
    lower_history_count h <= 2 ** 64 /\
    lower_history_pairs h pair /\ lower_history_current h pair q /\
    (!a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
      ?fn ai pre op sz post.
        lower_alloc_record h a fn ai pre op sz post) /\
    (!n p i fuel t r.
      n < LENGTH h /\ EL n h = BudgetStep n p i fuel (OK t) r /\
      i.inst_opcode = SETFMP ==>
      w2n root.bp_state.vs_initial_fmp <= w2n t.vs_fmp /\
      w2n t.vs_fmp <= w2n p.bp_state.vs_fmp) /\
    (!n p i fuel ret s_end s' r.
      n < LENGTH h /\ EL n h = BudgetReturn n p i fuel ret s_end s' r ==>
      i.inst_opcode <> DRET) ==>
    q.bp_state.vs_initial_fmp = root.bp_state.vs_initial_fmp /\
    w2n q.bp_state.vs_initial_fmp <= w2n q.bp_state.vs_fmp /\
    (!i sz_op sz.
      active_inst q.bp_fn i q.bp_state /\
      i.inst_opcode = DALLOCA /\
      i.inst_operands = [sz_op] /\
      eval_operand sz_op q.bp_state = SOME sz ==>
      w2n q.bp_state.vs_fmp + ceil32 (w2n sz) < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  `?charge. !a. a < LENGTH h /\ lower_event_allocates (EL a h) ==>
    ?fn ai pre op sz post.
      lower_alloc_record h a fn ai pre op sz post /\
      charge a = ceil32 (w2n sz)` by
    (simp[GSYM SKOLEM_THM, RIGHT_EXISTS_IMP_THM] >> metis_tac[]) >>
  drule_all lower_budget_history_allocation_charge_bound >> strip_tac >>
  `w2n root.bp_state.vs_initial_fmp +
    SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
      (GENLIST I (LENGTH h)))) < dimword (:256)` by metis_tac[] >>
  mp_tac lower_budget_path_fmp_envelope >>
  (impl_tac >-
    (conj_tac >- MATCH_ACCEPT_TAC lower_budget_step_fmp_interval >>
     rpt gen_tac >> strip_tac >>
     drule_all lower_budget_return_fmp_interval >> simp[])) >>
  disch_then drule >> disch_then (qspec_then `charge` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  `SUM (MAP charge (FILTER (\a. lower_event_allocates (EL a h))
    (GENLIST I (LENGTH h)))) <= lower_history_count h * 2 ** 64` by
    (qpat_x_assum `!i. active_inst q.bp_fn i q.bp_state /\ _ ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `w2n sz <= 32 * (2 ** 250 + 2 ** 59)` by
    (fs[lower_history_current_def] >> metis_tac[]) >>
  drule ceil32_le_multiple >>
  simp[contractABITheory.ceil32_def,
       fmpAlignmentTheory.ceil32_div_mul, MULT_COMM] >>
  strip_tac >>
  qspecl_then [`w2n root.bp_state.vs_initial_fmp`, `lower_history_count h`]
    mp_tac dalloca_split_budget >> simp[] >> strip_tac >> fs[] >> decide_tac
QED

