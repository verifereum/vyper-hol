(* Noncircular interfaces for fixed-horizon source execution instrumentation.
 * Outcome preservation is invoked at the preceding, already-valid prefix;
 * no goodness hypothesis about the final trace is used here. *)
Theory guardSourceInstrumentation
Ancestors
  vyperStorageFootprint vyperStorageTrace vyperCallOutcomeProps vyperCallOutcome

Theorem adopt_call_outcome_finite_prefix:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st.storage_trace /\
  (~rq.cr_static /\
   (outcome.co_success \/
    (rq.cr_kind <> MessageCall /\ rq.cr_kind <> DelegateMessageCall)) ==>
   storage_well_formed_on cx
     (empty_state with <|accounts := outcome.co_accounts;
                        tStorage := outcome.co_tStorage|>) (FST H)) /\
  adopt_call_outcome rq outcome st = (res,st') ==>
  storage_well_formed_on cx st' (FST H) /\
  storage_observations_ok cx H st'.storage_trace
Proof
  simp[adopt_call_outcome_equation] >>
  rpt IF_CASES_TAC >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[storage_observations_ok_append, storage_observations_ok_def,
      storage_trace_backends_well_formed_def,
      storage_trace_regions_def, storage_trace_locks_def,
      storage_roots_fit_def] >>
  gvs[storage_well_formed_on_def] >>
  map_every qx_gen_tac [`b`, `slot`, `tv`] >> strip_tac >>
  first_x_assum (drule_then mp_tac) >>
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

(* A successful take records an outcome but does not adopt it.  Thus the
 * valid prefix used below is st.storage_trace, not mid.storage_trace. *)
Theorem take_adopt_request_finite_prefix:
  valid_horizon cx initial_st H st.storage_trace /\
  storage_well_formed_on cx st (FST H) /\
  rq0.cr_accounts = st.accounts /\ rq0.cr_tStorage = st.tStorage /\
  take_request_outcome rq0 st = (INL (rq,outcome),mid) /\
  adopt_call_outcome rq outcome mid = (res,out) /\
  selected = st.storage_trace ++ StorageOutcome rq outcome :: suffix /\
  (!pre q co sfx.
    selected = pre ++ StorageOutcome q co :: sfx /\
    valid_horizon cx initial_st H pre /\
    storage_well_formed_on cx
      (empty_state with <|accounts := q.cr_accounts;
                         tStorage := q.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := co.co_accounts;
                         tStorage := co.co_tStorage|>) (FST H)) ==>
  storage_well_formed_on cx out (FST H) /\
  valid_horizon cx initial_st H out.storage_trace
Proof
  strip_tac >> drule take_request_outcome_success >> strip_tac >> gvs[] >>
  `storage_well_formed_on cx
     (empty_state with <|accounts := st.accounts; tStorage := st.tStorage|>)
     (FST H)` by
    (`storage_well_formed_on cx
        (empty_state with <|accounts := st.accounts; tStorage := st.tStorage|>)
        (FST H) <=> storage_well_formed_on cx st (FST H)` by
       (irule storage_well_formed_on_backends >> simp[]) >> gvs[]) >>
  `storage_well_formed_on cx
     (empty_state with <|accounts := outcome.co_accounts;
                        tStorage := outcome.co_tStorage|>) (FST H)` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[valid_horizon_def] >>
  drule_at (Pat `adopt_call_outcome _ _ _ = _`) adopt_call_outcome_finite_prefix >>
  disch_then (qspecl_then [`cx`, `H`] mp_tac) >>
  (impl_tac
   >- (simp[storage_observations_ok_append, storage_observations_ok_def,
            storage_trace_backends_well_formed_def, storage_trace_regions_def,
            storage_trace_locks_def, storage_roots_fit_def] >>
       `storage_well_formed_on cx
          (st with <|outcomes := SOME rest;
                     requests := record_request rq st.requests;
                     storage_trace := st.storage_trace ++ [StorageOutcome rq outcome]|>)
          (FST H) <=> storage_well_formed_on cx st (FST H)` by
         (irule storage_well_formed_on_backends >> simp[]) >>
       gvs[storage_observations_ok_def, storage_trace_backends_well_formed_def,
           storage_trace_regions_def, storage_trace_locks_def, storage_roots_fit_def])) >>
  simp[]
QED

(* Both IHs keep the SAME selected full trace.  Only the outgoing-prefix
 * witness changes.  In particular, the outcome rule is never strengthened
 * from one execution to all possible continuations. *)
Theorem finite_prefix_bind:
  (!v. storage_trace_frame (g v)) /\
  (!r t. f st = (r,t) /\ (?sfx. selected = t.storage_trace ++ sfx) ==>
    storage_well_formed_on cx t (FST H) /\
    storage_observations_ok cx H t.storage_trace) /\
  (!v s r t.
    storage_well_formed_on cx s (FST H) /\
    storage_observations_ok cx H s.storage_trace /\
    g v s = (r,t) /\ (?sfx. selected = t.storage_trace ++ sfx) ==>
    storage_well_formed_on cx t (FST H) /\
    storage_observations_ok cx H t.storage_trace) /\
  bind f g st = (res,out) /\
  (?sfx. selected = out.storage_trace ++ sfx) ==>
  storage_well_formed_on cx out (FST H) /\
  storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >> Cases_on `f st` >> rename1 `f st = (rr,mid)` >>
  Cases_on `rr` >> gvs[vyperStateTheory.bind_def, vyperStateTheory.raise_def]
  >- (rename1 `g v mid = (res,out)` >>
      `?delta. out.storage_trace = mid.storage_trace ++ delta` by
        metis_tac[storage_trace_frame_prefix] >>
      `?tail. out.storage_trace ++ sfx = mid.storage_trace ++ tail` by
        (qexists `delta ++ sfx` >> simp[]) >>
      `storage_well_formed_on cx mid (FST H) /\
       storage_observations_ok cx H mid.storage_trace` by
        (qpat_x_assum `(?sfx. _) ==> _` irule >> metis_tac[]) >>
      qpat_x_assum `!v s r t. _` irule >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* Validated mutual-interface schema (the mutual theorem itself is future work).
 *
 * Use the eleven clauses, in exactly the order and with exactly the typing
 * and runtime antecedents of eval_storage_well_formed_on_mutual:
 *   eval_stmt, eval_stmts, eval_iterator, eval_for, eval_expr, eval_exprs,
 *   eval_base_place, eval_target_place, assign_tuple_targets,
 *   assign_tuple_target_list, eval_expr_results.
 * Preserve the two well_typed_expr/type_place_expr implications in clause 5.
 * Quantify initial_st and selected AFTER the evaluator's structural arguments,
 * so recursive calls can use the same initial_st and selected.  Replace the
 * final storage_observations_ok premise in every clause with:
 *
 *   IS_SOME st.outcomes /\
 *   valid_horizon cx initial_st H st.storage_trace /\
 *   (?sfx. selected = st'.storage_trace ++ sfx) /\
 *   EVERY (\r. MEM r (FST H)) (storage_trace_regions selected) /\
 *   EVERY (\l. MEM l (SND H)) (storage_trace_locks selected) /\
 *   storage_roots_fit selected /\
 *   (!pre rq co sfx.
 *      selected = pre ++ StorageOutcome rq co :: sfx /\
 *      valid_horizon cx initial_st H pre /\
 *      storage_well_formed_on cx
 *        (empty_state with <|accounts := rq.cr_accounts;
 *                           tStorage := rq.cr_tStorage|>) (FST H) ==>
 *      storage_well_formed_on cx
 *        (empty_state with <|accounts := co.co_accounts;
 *                           tStorage := co.co_tStorage|>) (FST H))
 *
 * The conclusion in every clause is the old current-state conclusion AND
 * storage_observations_ok cx H st'.storage_trace (under the same typing
 * implication in clause 5).  The initial state's fixed-H goodness remains
 * an independent antecedent: the incoming trace need not contain a backend.
 *
 * finite_prefix_bind checks the sequencing invariant, including exceptions.
 * The global selected parameter avoids any need to extend a prefix-specific
 * outcome rule to unseen continuations.  At each take, the old trace is
 * already good; recording StorageOutcome itself changes no backend.  At
 * adoption, the outcome rule supplies the new backend before it is recorded.
 * take_create_outcome_success has exactly the same unchanged-backend and
 * appended-event shape as take_request_outcome_success (its runtime account
 * guard is stronger).  adopt_call_outcome_finite_prefix covers create-kind
 * failure adoption as well as message success, static, and message failure.
 *
 * IS_SOME is essential: otherwise the non-oracle run_raw_call branch needs
 * a separate callee-preservation premise not expressed by StorageOutcome.
 * It is available at call_external_trace (SOME os), and is threaded through
 * recursion by eval_outcome_suffix_mutual and outcome_suffix_modes; the
 * expression-results clause uses eval_expr_results_outcome_suffix.
 *
 * Internal calls change stk, not txn.target, and temporarily change scopes.
 * Their defaults/body/cleanup proof obligations are the ones in
 * vyperFiniteStoragePreservation's Expr_Call_IntCall and IntCall_* resumes.
 * Its existing local storage_well_formed_on_stk/_scopes and
 * storage_observations_ok_stk interfaces must be exported/relocated for reuse,
 * not copied.  The same applies to call-footprint's local target-invariance
 * and entry/lock/unlock helpers when proving the external wrapper.
 * At entry cx.in_deploy = F, hence constant_trace = []; SOME os establishes
 * oracle mode.  Cleanup can append locks but cannot discard backend events,
 * even on a source rollback: call_external_function_trace keeps the failed
 * state's requests and storage_trace while returning the original machine.
 * Thus the strengthened theorem must cover exceptional results too.
 *)
