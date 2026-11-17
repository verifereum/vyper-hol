(* Pending-allocation credit along recorder histories.
 *
 * A DALLOCA that is active, or executed but not yet paired with its
 * consuming CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2, reserves one unit
 * of the call budget for that consumer. Unlike the exit certificate's
 * allocation fields, this bound is preserved step by step: executing the
 * consumer moves the reserved unit into the consumed count.
 *
 * TOP-LEVEL:
 *   lower_alloc_credit                     - the credit invariant
 *   lower_alloc_credit_fields              - it gives the certificate's
 *                                            allocation fields
 *   lower_vyper_runtime_unit_alloc_credit  - the compiled runtime unit's
 *                                            recorder paths keep it
 *)
Theory loweringAllocCredit
Ancestors
  loweringCallBudgetHistory compileVyper vyperCompiler vyperLoweringCorrect
  e2eDefs sourceCallCount exprSimHypsDefs lowerDloadDefs contextRawReachable
  venomLayout list rich_list arithmetic

Definition lower_alloc_pending_def:
  lower_alloc_pending h pair q <=>
    (?a. a < LENGTH h /\ lower_event_allocates (EL a h) /\
         pair a = LENGTH h) \/
    (?i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA)
End

Definition lower_alloc_credit_def:
  lower_alloc_credit k h q <=>
    ?pair.
      lower_history_count h +
        (if lower_alloc_pending h pair q then 1 else 0) <= k /\
      lower_history_pairs h pair /\ lower_history_current h pair q /\
      (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
        ?fn i s op sz t. lower_alloc_record h n fn i s op sz t)
End

Theorem lower_alloc_credit_fields:
  !k h q.
    lower_alloc_credit k h q ==>
    lower_history_count h <= k /\
    ?pair.
      LENGTH (FILTER lower_event_allocates h) <= k /\
      (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
        SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
      lower_history_pairs h pair /\ lower_history_current h pair q /\
      (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
        ?fn i s op sz t. lower_alloc_record h n fn i s op sz t)
Proof
  rw[lower_alloc_credit_def] >>
  drule_all lower_budget_completed_pairs_count >> strip_tac >>
  drule lower_budget_pairs_count >> strip_tac >>
  Cases_on `lower_alloc_pending h pair q` >> fs[]
  >- (qexists_tac `pair` >> rw[] >>
      `LENGTH (FILTER lower_event_allocates h) <= lower_history_count h` by
        metis_tac[] >> decide_tac) >>
  `FILTER (\a. lower_event_allocates (EL a h) /\ pair a < LENGTH h)
     (GENLIST I (LENGTH h)) =
   FILTER (\a. lower_event_allocates (EL a h)) (GENLIST I (LENGTH h))` by
    (rw[FILTER_EQ, MEM_GENLIST] >> eq_tac >> rw[] >>
     fs[lower_history_pairs_def, lower_alloc_pending_def] >>
     first_x_assum drule_all >> rw[] >> fs[] >> metis_tac[]) >>
  `LENGTH (FILTER (\a. lower_event_allocates (EL a h))
     (GENLIST I (LENGTH h))) = LENGTH (FILTER lower_event_allocates h)` by
    (mp_tac (AP_TERM ``LENGTH : lower_budget_event list -> num`` (ISPECL [``lower_event_allocates``,
       ``\a:num. EL a (h:lower_budget_event list)``,
       ``GENLIST I (LENGTH (h:lower_budget_event list))``] FILTER_MAP)) >>
     simp[MAP_GENLIST, combinTheory.o_DEF, GENLIST_ID]) >>
  fs[lower_alloc_pending_def] >>
  qexists_tac `pair` >> rw[] >> metis_tac[]
QED

(* The gate-free supplier of the credit for the compiled runtime unit: the
   premises of the call-budget producer quotation in
   loweringCallBudgetHistory, with no DALLOCA exclusion. *)
Theorem lower_vyper_runtime_unit_alloc_credit:
  !tops rpolicy unit am tx ret vs k.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    k <= 2 ** 64 /\
    (!obs. source_calls_within k am tx vs.vs_outcomes obs) /\
    (!marks.
      source_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings) /\
      call_outcomes_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings)) /\
    (!marks. ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !D lo explicit name fn lbl entered p h marks q.
      unit.cu_context.ctx_entry = SOME name /\
      lookup_function name unit.cu_context.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl /\
      enters_block fn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) entered /\
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
             bp_taint := entry_taint; bp_fn := fn; bp_state := entered |> /\
      lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q ==>
      lower_alloc_credit k h q
Proof
  cheat
QED
