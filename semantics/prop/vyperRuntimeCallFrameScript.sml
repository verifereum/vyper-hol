(* Conditional exact immutable frame at the external-call boundary. *)
Theory vyperRuntimeCallFrame
Ancestors
  vyperInterpreter vyperState vyperContext vyperMisc vyperValue
  vyperTypeContractSoundness vyperStatePreservation
  list rich_list finite_map

Theorem eval_external_defaults_immutables_frame:
  (!st r st'. eval_exprs cx es st = (r,st') ==>
    st'.immutables = st.immutables) /\
  eval_external_defaults cx es st = (r,st') ==>
  st'.immutables = st.immutables
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem call_external_function_trace_runtime_frame:
  ~cx.in_deploy /\
  (!st r st'.
    eval_exprs cx (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) st = (r,st') ==>
    st'.immutables = st.immutables) /\
  (!st r st'. eval_stmts cx (bdy : stmt list) st = (r,st') ==>
    st'.immutables = st.immutables) /\
  call_external_function_trace orc gobs am cx nr mut ts all_mods args dflts vals bdy ret = (res,am',rqs,observations) ==>
  am'.immutables = am.immutables
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_trace_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  IF_CASES_TAC >- simp[] >>
  qmatch_goalsub_abbrev_tac `ignore_bind send rest st0` >>
  `!r st'. ignore_bind send rest st0 = (r,st') ==> st'.immutables = st0.immutables` by
    (unabbrev_all_tac >>
     simp[bind_def, ignore_bind_def, set_scopes_def,
          Excl "lock_if_nr_def"] >>
     rpt gen_tac >>
     simp[option_CASE_rator, AllCaseEqs(), PULL_EXISTS,
          Excl "lock_if_nr_def"] >> rpt strip_tac >>
     gvs[raise_def, bind_def, set_scopes_def, Excl "lock_if_nr_def"] >>
     imp_res_tac send_call_value_preserves_immutables >>
     imp_res_tac eval_external_defaults_immutables_frame >>
     imp_res_tac call_lock_action_preserves_immutables >>
     gvs[Excl "lock_if_nr_def"] >>
     gvs[return_def, AllCaseEqs(), Excl "lock_if_nr_def"] >>
     imp_res_tac (REWRITE_RULE [GSYM lock_if_nr_def]
       call_lock_action_preserves_immutables) >>
     gvs[Excl "lock_if_nr_def"] >> metis_tac[]) >>
  `!st r st'. unlock_if_nr cx nr (mut = View \/ mut = Pure) st = (r,st') ==>
    st'.immutables = st.immutables` by
    (rpt gen_tac >> simp[unlock_if_nr_def] >>
     IF_CASES_TAC >- (Cases_on `cx.nonreentrant_slot` >>
       simp[return_def] >> metis_tac[release_nonreentrant_lock_immutables]) >>
     simp[return_def]) >>
  Cases_on `ignore_bind send rest st0` >>
  rename1 `ignore_bind send rest st0 = (result, st1)` >>
  Cases_on `unlock_if_nr cx nr (mut = View \/ mut = Pure) st1` >>
  rename1 `unlock_if_nr cx nr (mut = View \/ mut = Pure) st1 = (unlocked, st2)` >>
  `st0.immutables = am.immutables` by simp[Abbr `st0`, initial_state_def] >>
  Cases_on `result`
  >- (Cases_on `unlocked` >>
      gvs[AllCaseEqs(), Excl "unlock_if_nr_def"] >> rpt strip_tac >>
      gvs[abstract_machine_from_state_def, Excl "unlock_if_nr_def"] >>
      metis_tac[]) >>
  rename1 `ignore_bind send rest st0 = (INR exc,st1)` >>
  Cases_on `exc` >> Cases_on `unlocked` >>
  gvs[AllCaseEqs(), PULL_EXISTS, Excl "unlock_if_nr_def"] >>
  rpt strip_tac >> gvs[Excl "unlock_if_nr_def"] >>
  simp[abstract_machine_from_state_def] >>
  `st0.immutables = am.immutables` by simp[Abbr `st0`, initial_state_def] >>
  Cases_on `evaluate_type (type_env_all_modules all_mods) ret` >>
  gvs[AllCaseEqs(), Excl "unlock_if_nr_def"] >>
  rename1 `safe_cast tv value` >>
  Cases_on `safe_cast tv value` >>
  gvs[abstract_machine_from_state_def] >> metis_tac[]
QED
