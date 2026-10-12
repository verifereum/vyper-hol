(* Actual evaluator outcome suffix, including errors. NONE retains its field;
 * activated ordinary ExtCall consumes a head before even a failed return. *)
Theory vyperEvalOutcomeSuffix
Ancestors
  list pair option vyperMisc vyperState vyperInterpreter vyperCreate
  vyperStatePreservation vyperCallFrame vyperStorageBackend vyperCallOutcome
Libs monadsyntax

Definition outcomes_frame_def:
  outcomes_frame f <=> !st. (SND (f st)).outcomes = st.outcomes
End

Theorem outcomes_frame_result:
  outcomes_frame f /\ f st = (res,st') ==> st'.outcomes = st.outcomes
Proof
  simp[outcomes_frame_def] >> strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem outcomes_frame_return[simp]:
  outcomes_frame (return x)
Proof
  simp[outcomes_frame_def, return_def]
QED

Theorem outcomes_frame_raise[simp]:
  outcomes_frame (raise e)
Proof
  simp[outcomes_frame_def, raise_def]
QED

Theorem outcomes_frame_bind[simp]:
  outcomes_frame f /\ (!v. outcomes_frame (g v)) ==>
  outcomes_frame (monad_bind f g)
Proof
  simp[outcomes_frame_def, bind_def, FORALL_PROD] >>
  rpt strip_tac >> Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  qpat_x_assum `!st. _` (qspec_then `st` mp_tac) >> simp[] >>
  TRY (qpat_x_assum `!v st. _` (qspecl_then [`x`,`r`] mp_tac)) >> simp[]
QED

Theorem outcomes_frame_ignore_bind[simp]:
  outcomes_frame f /\ outcomes_frame g ==>
  outcomes_frame (do f; g od)
Proof
  simp[ignore_bind_def]
QED

Theorem outcomes_frame_cond[simp]:
  outcomes_frame f /\ outcomes_frame g ==>
  outcomes_frame (if b then f else g)
Proof
  Cases_on `b` >> simp[]
QED

Theorem outcomes_frame_try[simp]:
  outcomes_frame f /\ (!e. outcomes_frame (h e)) ==>
  outcomes_frame (try f h)
Proof
  simp[outcomes_frame_def, try_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  qpat_x_assum `!st. _` (qspec_then `st` mp_tac) >> simp[] >>
  TRY (qpat_x_assum `!e st. _` (qspecl_then [`y`,`r`] mp_tac)) >> simp[]
QED

Theorem outcomes_frame_finally[simp]:
  outcomes_frame f /\ outcomes_frame g ==>
  outcomes_frame (finally f g)
Proof
  simp[outcomes_frame_def, finally_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `g r` >> Cases_on `q'` >> gvs[] >>
  qpat_x_assum `!st. (SND (f st)).outcomes = _` (qspec_then `st` mp_tac) >>
  qpat_x_assum `!st. (SND (g st)).outcomes = _` (qspec_then `r` mp_tac) >>
  Cases_on `q` >> simp[ignore_bind_def, bind_def, return_def, raise_def]
QED

Theorem outcomes_frame_state_preserving[local]:
  (!st res st'. f st = (res,st') ==> st' = st) ==> outcomes_frame f
Proof
  simp[outcomes_frame_def] >> rpt strip_tac >> Cases_on `f st` >>
  first_x_assum drule >> simp[]
QED

Theorem outcomes_frame_reads[simp]:
  outcomes_frame (get_Value tv) /\
  outcomes_frame get_accounts /\ outcomes_frame get_transient_storage /\
  outcomes_frame (materialise cx tv) /\
  outcomes_frame (lookup_global cx src n) /\
  outcomes_frame (lookup_flag_mem cx nsid mid) /\
  outcomes_frame (read_storage_slot cx b slot ty) /\
  outcomes_frame (check_array_bounds cx tv v) /\
  outcomes_frame (toplevel_array_length cx tv) /\
  outcomes_frame (lift_option_type x msg) /\
  outcomes_frame (lift_option y msg) /\
  outcomes_frame (lift_sum z) /\ outcomes_frame (lift_sum_runtime zr)
Proof
  rpt conj_tac >> irule outcomes_frame_state_preserving >>
  rpt strip_tac >> FIRST [drule_all get_Value_state, drule_all get_accounts_state,
    drule_all get_transient_storage_state, drule_all materialise_state,
    drule_all lookup_global_state, drule_all lookup_flag_mem_state,
    drule_all read_storage_slot_state, drule_all check_array_bounds_state,
    drule_all toplevel_array_length_state, drule_all lift_option_type_state,
    drule_all lift_option_state, drule_all lift_sum_state,
    drule_all lift_sum_runtime_state] >> simp[]
QED

Theorem outcomes_frame_primitives[simp]:
  outcomes_frame (check b msg) /\ outcomes_frame (type_check b msg) /\
  outcomes_frame get_scopes /\ outcomes_frame (set_scopes scs) /\
  outcomes_frame push_scope /\ outcomes_frame pop_scope /\
  outcomes_frame (push_scope_with_var nm ty v) /\
  outcomes_frame (new_variable id ty v) /\
  outcomes_frame (update_accounts fa) /\ outcomes_frame (update_transient ft) /\
  outcomes_frame (append_logs ls) /\ outcomes_frame (push_log lg) /\
  outcomes_frame (get_immutables cx src) /\
  outcomes_frame (set_immutable cx src nm ty v) /\
  outcomes_frame (get_storage_backend cx transient) /\
  outcomes_frame (write_storage_slot cx transient slot ty v) /\
  outcomes_frame (set_global cx src nm v) /\
  outcomes_frame (transfer_value sender target amount) /\
  outcomes_frame (acquire_nonreentrant_lock target lock view) /\
  outcomes_frame (release_nonreentrant_lock target lock) /\
  outcomes_frame (push_function fn sc cx) /\ outcomes_frame (pop_function scs)
Proof
  simp[outcomes_frame_def, check_def, type_check_def, assert_def,
    get_scopes_def, set_scopes_def, push_scope_def, pop_scope_def,
    push_scope_with_var_def, new_variable_def, update_accounts_def,
    update_transient_def, append_logs_def, push_log_def,
    get_immutables_def, get_address_immutables_def,
    set_immutable_def, set_address_immutables_def,
    get_storage_backend_def, set_storage_backend_def, write_storage_slot_def,
    set_global_def, transfer_value_def, get_accounts_def,
    acquire_nonreentrant_lock_def, release_nonreentrant_lock_def,
    get_transient_storage_def, push_function_def, pop_function_def,
    bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> rpt CASE_TAC >>
  gvs[set_scopes_def, update_accounts_def, update_transient_def,
      set_address_immutables_def, get_storage_backend_def,
      set_storage_backend_def, write_storage_slot_def,
      lift_option_type_def, lift_option_def, lift_sum_def,
      get_accounts_def, get_transient_storage_def, check_def,
      type_check_def, assert_def,
      bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[get_storage_backend_eq, set_storage_backend_eq,
      option_CASE_rator, prod_CASE_rator, COND_RATOR,
      return_def, raise_def, AllCaseEqs()] >>
  rpt CASE_TAC >>
  gvs[get_storage_backend_eq, set_storage_backend_eq, set_storage_def,
      return_def, raise_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `set_storage _ _ backend _` >>
  Cases_on `backend` >> simp[set_storage_def]
QED

Theorem outcomes_frame_switch[simp]:
  outcomes_frame f /\ outcomes_frame g ==>
  outcomes_frame (switch_BoolV tv f g)
Proof
  Cases_on `tv` >> simp[switch_BoolV_def] >> Cases_on `v` >> simp[]
QED

Theorem outcomes_frame_handlers[simp]:
  outcomes_frame (handle_loop_exception e) /\
  outcomes_frame (handle_function e)
Proof
  Cases_on `e` >> simp[handle_loop_exception_def, handle_function_def]
QED

Theorem outcomes_frame_assign_result[simp]:
  outcomes_frame (assign_result tv op v subs)
Proof
  Cases_on `op` >> simp[assign_result_def]
QED

Theorem outcomes_frame_resolve_array[simp]:
  outcomes_frame (resolve_array_element cx b slot tv subs)
Proof
  irule outcomes_frame_state_preserving >>
  metis_tac[resolve_array_element_state]
QED

Theorem outcomes_frame_assignment:
  (!cx tgt op. outcomes_frame (assign_target cx tgt op)) /\
  (!cx tgts vs. outcomes_frame (assign_targets cx tgts vs))
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once assign_target_def, FORALL_PROD] >> rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[FORALL_PROD]),
    irule outcomes_frame_bind >> conj_tac,
    irule outcomes_frame_ignore_bind >> conj_tac,
    irule outcomes_frame_cond >> conj_tac,
    gen_tac, CASE_TAC])
QED

Theorem outcomes_frame_bind_guarded:
  outcomes_frame f /\
  (!s v t. f s = (INL v,t) ==> outcomes_frame (g v)) ==>
  outcomes_frame (monad_bind f g)
Proof
  simp[outcomes_frame_def, bind_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  `r.outcomes = st.outcomes` by
    (qpat_x_assum `!st. (SND (f st)).outcomes = _`
       (qspec_then `st` mp_tac) >> simp[]) >> gvs[] >>
  qpat_x_assum `!s v t. _` (qspecl_then [`st`,`x`,`r`] mp_tac) >>
  simp[] >> disch_then (qspec_then `r` mp_tac) >> simp[]
QED

val OUTCOMES_FRAME_TAC =
  rpt (FIRST [CHANGED_TAC (simp_tac bool_ss
      [FORALL_PROD, pair_case_thm, UNCURRY, outcomes_frame_assignment, outcomes_frame_reads,
       outcomes_frame_primitives, outcomes_frame_handlers,
       outcomes_frame_return, outcomes_frame_raise]),
    first_assum ACCEPT_TAC,
    CHANGED_TAC (fn (asl,w) =>
      simp_tac (bool_ss ++ numSimps.ARITH_ss) (pair_case_thm :: UNCURRY ::
        List.map ASSUME (List.filter is_eq asl)) (asl,w)),
    irule outcomes_frame_bind_guarded >> conj_tac,
    CHANGED_TAC (rewrite_tac[ignore_bind_def]),
    irule outcomes_frame_finally >> conj_tac,
    irule outcomes_frame_try >> conj_tac,
    CHANGED_TAC (simp_tac bool_ss [switch_BoolV_def]),
    gen_tac, strip_tac,
    first_assum (irule_at Any),
    first_assum MATCH_MP_TAC, conj_tac, CASE_TAC]);

Theorem outcomes_frame_create[simp]:
  outcomes_frame (eval_create cx kind has_salt rof arg_tys vs)
Proof
  simp[eval_create_def, create_soft_failure_def] >>
  rpt (FIRST [CHANGED_TAC (simp[FORALL_PROD]),
    irule outcomes_frame_bind >> conj_tac,
    irule outcomes_frame_ignore_bind >> conj_tac,
    irule outcomes_frame_cond >> conj_tac,
    gen_tac, CASE_TAC])
QED

(* TASK032: the independent vyperExtCallConsumptionTest witness disproves the
   unconditional evaluator frame. Original statement and proof retained.
Theorem eval_outcomes_frame_mutual:
  (!cx s. outcomes_frame (eval_stmt cx s)) /\
  (!cx ss. outcomes_frame (eval_stmts cx ss)) /\
  (!cx it. outcomes_frame (eval_iterator cx it)) /\
  (!cx tgt. outcomes_frame (eval_target cx tgt)) /\
  (!cx tgts. outcomes_frame (eval_targets cx tgts)) /\
  (!cx bt. outcomes_frame (eval_base_target cx bt)) /\
  (!cx tyv id body vs. outcomes_frame (eval_for cx tyv id body vs)) /\
  (!cx e. outcomes_frame (eval_expr cx e)) /\
  (!cx es. outcomes_frame (eval_exprs cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY strip_tac >>
  simp[Once evaluate_def] >> OUTCOMES_FRAME_TAC
QED

*)

(* Lock primitives retain the residual outcome field, on success and error. *)
Theorem lock_outcomes_preserved:
  (acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
    st'.outcomes = st.outcomes) /\
  (release_nonreentrant_lock addr slot st = (res,st') ==>
    st'.outcomes = st.outcomes)
Proof
  conj_tac >> strip_tac >>
  first_assum (fn th =>
    let val result = #1 (pairSyntax.dest_pair (rhs (concl th))) in
      irule (INST_TYPE [alpha |-> type_of result] outcomes_frame_result) >>
      exists_tac (rator (lhs (concl th))) >> exists_tac result
    end) >> simp[]
QED

Definition outcome_suffix_def:
  outcome_suffix before after <=>
    (before = NONE /\ after = NONE) \/
    (?os prefix rest. before = SOME os /\ after = SOME rest /\
                      os = prefix ++ rest)
End

Theorem outcome_suffix_refl[simp]:
  outcome_suffix os os
Proof
  Cases_on `os` >> simp[outcome_suffix_def] >> qexists_tac `[]` >> simp[]
QED

Theorem outcome_suffix_trans:
  outcome_suffix os mid /\ outcome_suffix mid rest ==>
  outcome_suffix os rest
Proof
  simp[outcome_suffix_def] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_rename_tac `p ++ (q ++ xs)` >>
  qexists_tac `p ++ q` >> simp[APPEND_ASSOC]
QED

(* The relational invariant preserves NONE/SOME mode; SOME results are
   genuine suffixes, not arbitrary future lists. *)
Theorem outcome_suffix_modes:
  outcome_suffix before after ==>
  (before = NONE <=> after = NONE) /\
  (!os. before = SOME os ==>
    ?prefix rest. after = SOME rest /\ os = prefix ++ rest)
Proof
  simp[outcome_suffix_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `prefix` >> simp[]
QED

Theorem outcome_suffix_EVERY:
  outcome_suffix before after /\
  (!os. before = SOME os ==> EVERY P os) ==>
  (!rest. after = SOME rest ==> EVERY P rest)
Proof
  simp[outcome_suffix_def] >> rpt strip_tac >> gvs[EVERY_APPEND]
QED

(* TASK032: unconditional SOME equality is false (actual activated witness).
   Original statement and proof retained, not admitted.
Theorem eval_outcomes_preserved_mutual:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx tgt st res st'. eval_target cx tgt st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx tgts st res st'. eval_targets cx tgts st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx bt st res st'. eval_base_target cx bt st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx tyv id body vs st res st'. eval_for cx tyv id body vs st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> st'.outcomes = st.outcomes)
Proof
  rpt conj_tac >> rpt strip_tac >>
  first_assum (fn th =>
    let val result = #1 (pairSyntax.dest_pair (rhs (concl th))) in
      irule (INST_TYPE [alpha |-> type_of result] outcomes_frame_result) >>
      exists_tac (rator (lhs (concl th))) >> exists_tac result
    end) >>
  simp[eval_outcomes_frame_mutual]
QED

*)

Definition outcomes_suffix_def:
  outcomes_suffix f <=> !st. outcome_suffix st.outcomes (SND (f st)).outcomes
End

Theorem outcomes_suffix_result:
  outcomes_suffix f /\ f st = (res,st') ==>
  outcome_suffix st.outcomes st'.outcomes
Proof
  simp[outcomes_suffix_def] >> strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[]
QED

Theorem outcomes_suffix_frame:
  outcomes_frame f ==> outcomes_suffix f
Proof
  simp[outcomes_frame_def, outcomes_suffix_def]
QED

Theorem outcomes_suffix_read:
  outcomes_suffix (λst. return (g st) st)
Proof
  simp[outcomes_suffix_def, return_def]
QED

Theorem outcomes_suffix_bind_guarded:
  outcomes_suffix f /\
  (!s v t. f s = (INL v,t) ==> outcomes_suffix (g v)) ==>
  outcomes_suffix (monad_bind f g)
Proof
  simp[outcomes_suffix_def, bind_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  `outcome_suffix st.outcomes r.outcomes` by
    (qpat_x_assum `!st. outcome_suffix _ (SND (f st)).outcomes`
       (qspec_then `st` mp_tac) >> simp[]) >>
  TRY (qpat_x_assum `!s v t. _` (qspecl_then [`st`,`x`,`r`] mp_tac) >>
    simp[] >> disch_then (qspec_then `r` mp_tac) >>
    strip_tac >> drule_all outcome_suffix_trans >> simp[])
QED

Theorem outcomes_suffix_try:
  outcomes_suffix f /\ (!e. outcomes_suffix (h e)) ==>
  outcomes_suffix (try f h)
Proof
  simp[outcomes_suffix_def, try_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  qpat_x_assum `!st. outcome_suffix _ (SND (f st)).outcomes`
    (qspec_then `st` mp_tac) >> simp[] >> strip_tac >>
  TRY (qpat_x_assum `!e st. _` (qspecl_then [`y`,`r`] mp_tac) >>
    strip_tac >> drule_all outcome_suffix_trans >> simp[])
QED

Theorem outcomes_suffix_finally:
  outcomes_suffix f /\ outcomes_suffix g ==>
  outcomes_suffix (finally f g)
Proof
  simp[outcomes_suffix_def, finally_def] >> rpt strip_tac >>
  Cases_on `f st` >> Cases_on `g r` >> Cases_on `q'` >> gvs[] >>
  qpat_x_assum `!st. outcome_suffix _ (SND (f st)).outcomes`
    (qspec_then `st` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!st. outcome_suffix _ (SND (g st)).outcomes`
    (qspec_then `r` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `q` >> simp[ignore_bind_def, bind_def, return_def, raise_def] >>
  drule_all outcome_suffix_trans >> simp[]
QED

Theorem outcomes_suffix_take:
  outcomes_suffix (take_call_outcome target calldata value_opt)
Proof
  simp[outcomes_suffix_def] >> gen_tac >>
  Cases_on `take_call_outcome target calldata value_opt st` >>
  Cases_on `st.outcomes`
  >- gvs[take_call_outcome_NONE] >>
  drule_all take_call_outcome_suffix >> strip_tac >>
  simp[outcome_suffix_def] >> qexists_tac `prefix` >> simp[]
QED

Theorem outcomes_frame_adopt:
  outcomes_frame (adopt_call_outcome rq co)
Proof
  simp[outcomes_frame_def, adopt_call_outcome_def, extCallOracleTheory.adopt_outcome_def,
       return_def] >> rpt gen_tac >> CASE_TAC >> simp[]
QED

(* Precompute the unconditional suffix facts. Using outcomes_suffix_frame
   as a conditional rewrite makes simp retry a frame proof for every compound
   monadic term, including recursive evaluators that can consume outcomes. *)
val outcomes_suffix_frame_simps =
  List.map (GEN_ALL o MATCH_MP outcomes_suffix_frame o SPEC_ALL)
    (List.concat (List.map (CONJUNCTS o SPEC_ALL)
      [outcomes_frame_assignment, outcomes_frame_reads,
       outcomes_frame_primitives, outcomes_frame_handlers,
       outcomes_frame_return, outcomes_frame_raise, outcomes_frame_create,
       outcomes_frame_assign_result, outcomes_frame_resolve_array,
       outcomes_frame_adopt]));

val OUTCOMES_SUFFIX_TAC =
  rpt (FIRST [CHANGED_TAC (simp_tac bool_ss
      ([FORALL_PROD, pair_case_thm, UNCURRY] @ outcomes_suffix_frame_simps)),
    first_assum ACCEPT_TAC,
    MATCH_ACCEPT_TAC outcomes_suffix_read,
    MATCH_ACCEPT_TAC outcomes_suffix_take,
    CHANGED_TAC (fn (asl,w) =>
      simp_tac (bool_ss ++ numSimps.ARITH_ss) (pair_case_thm :: UNCURRY ::
        List.map ASSUME (List.filter is_eq asl)) (asl,w)),
    irule outcomes_suffix_bind_guarded >> conj_tac,
    CHANGED_TAC (rewrite_tac[ignore_bind_def]),
    irule outcomes_suffix_finally >> conj_tac,
    irule outcomes_suffix_try >> conj_tac,
    CHANGED_TAC (simp_tac bool_ss [switch_BoolV_def]),
    gen_tac, (strip_tac >> fs[ignore_bind_def]),
    conj_tac, CASE_TAC]);

Theorem eval_outcomes_suffix_mutual:
  (!cx s. outcomes_suffix (eval_stmt cx s)) /\
  (!cx ss. outcomes_suffix (eval_stmts cx ss)) /\
  (!cx it. outcomes_suffix (eval_iterator cx it)) /\
  (!cx tgt. outcomes_suffix (eval_target cx tgt)) /\
  (!cx tgts. outcomes_suffix (eval_targets cx tgts)) /\
  (!cx bt. outcomes_suffix (eval_base_target cx bt)) /\
  (!cx tyv id body vs. outcomes_suffix (eval_for cx tyv id body vs)) /\
  (!cx e. outcomes_suffix (eval_expr cx e)) /\
  (!cx es. outcomes_suffix (eval_exprs cx es))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY strip_tac >> TRY (rename1 `ExtCall` >> suspend "ExtCall") >>
  simp[Once evaluate_def] >> OUTCOMES_SUFFIX_TAC >> OUTCOMES_FRAME_TAC >>
  rpt (FIRST [first_assum ACCEPT_TAC,
    first_x_assum (fn th => drule_at Any th >> simp[] >> strip_tac)])
QED

Resume eval_outcomes_suffix_mutual[ExtCall]:
  simp[Once evaluate_def] >> OUTCOMES_SUFFIX_TAC >>
  rpt (FIRST [first_assum ACCEPT_TAC,
    first_x_assum (fn th => drule_at Any th >> simp[] >> strip_tac)])
QED

Finalise eval_outcomes_suffix_mutual

Theorem eval_outcome_suffix_mutual:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx tgt st res st'. eval_target cx tgt st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx tgts st res st'. eval_targets cx tgts st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx bt st res st'. eval_base_target cx bt st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx tyv id body vs st res st'. eval_for cx tyv id body vs st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> outcome_suffix st.outcomes st'.outcomes)
Proof
  rpt conj_tac >> rpt strip_tac >>
  first_assum (fn th =>
    let val result = #1 (pairSyntax.dest_pair (rhs (concl th))) in
      irule (INST_TYPE [alpha |-> type_of result] outcomes_suffix_result) >>
      exists_tac (rator (lhs (concl th))) >> exists_tac result
    end) >> simp[eval_outcomes_suffix_mutual]
QED

(* Minimal true replacement: the NONE field is preserved, on every result.
   SOME execution is governed by the independently proved suffix above. *)
Theorem eval_outcomes_preserved_mutual:
  (!cx s st res st'. st.outcomes = NONE /\ eval_stmt cx s st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx ss st res st'. st.outcomes = NONE /\ eval_stmts cx ss st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx it st res st'. st.outcomes = NONE /\ eval_iterator cx it st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx tgt st res st'. st.outcomes = NONE /\ eval_target cx tgt st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx tgts st res st'. st.outcomes = NONE /\ eval_targets cx tgts st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx bt st res st'. st.outcomes = NONE /\ eval_base_target cx bt st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx tyv id body vs st res st'. st.outcomes = NONE /\ eval_for cx tyv id body vs st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx e st res st'. st.outcomes = NONE /\ eval_expr cx e st = (res,st') ==> st'.outcomes = st.outcomes) /\
  (!cx es st res st'. st.outcomes = NONE /\ eval_exprs cx es st = (res,st') ==> st'.outcomes = st.outcomes)
Proof
  rpt conj_tac >> rpt strip_tac >> imp_res_tac eval_outcome_suffix_mutual >>
  gvs[outcome_suffix_def]
QED

Definition outcomes_NONE_frame_def:
  outcomes_NONE_frame f <=>
    !st. st.outcomes = NONE ==> (SND (f st)).outcomes = st.outcomes
End

Theorem eval_outcomes_frame_mutual:
  (!cx s. outcomes_NONE_frame (eval_stmt cx s)) /\
  (!cx ss. outcomes_NONE_frame (eval_stmts cx ss)) /\
  (!cx it. outcomes_NONE_frame (eval_iterator cx it)) /\
  (!cx tgt. outcomes_NONE_frame (eval_target cx tgt)) /\
  (!cx tgts. outcomes_NONE_frame (eval_targets cx tgts)) /\
  (!cx bt. outcomes_NONE_frame (eval_base_target cx bt)) /\
  (!cx tyv id body vs. outcomes_NONE_frame (eval_for cx tyv id body vs)) /\
  (!cx e. outcomes_NONE_frame (eval_expr cx e)) /\
  (!cx es. outcomes_NONE_frame (eval_exprs cx es))
Proof
  simp[outcomes_NONE_frame_def] >> rpt conj_tac >> rpt strip_tac >>
  imp_res_tac eval_outcomes_preserved_mutual >>
  metis_tac[PAIR, SND]
QED
