(* Actual recorded allocation charges, conditional on recorder invariants. *)
Theory loweringCallBudgetBounds
Ancestors
  loweringCallBudgetHistory dallocaBounds calleeTransport venomExecProofs
  words arithmetic list rich_list pred_set

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

