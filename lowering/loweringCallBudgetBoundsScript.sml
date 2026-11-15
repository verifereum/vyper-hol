(* Actual recorded allocation charges, conditional on recorder invariants. *)
Theory loweringCallBudgetBounds
Ancestors
  loweringCallBudgetHistory dallocaBounds calleeTransport venomExecProofs
  words arithmetic list rich_list pred_set

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

