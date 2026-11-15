(* Actual recorded allocation charges, conditional on recorder invariants. *)
Theory loweringCallBudgetBounds
Ancestors
  loweringCallBudgetHistory dallocaBounds calleeTransport venomExecProofs
  words arithmetic list rich_list pred_set

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

