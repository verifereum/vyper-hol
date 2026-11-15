(* Checked getter entries preserve a selected fixed-horizon trace prefix. *)
Theory guardSourceGetter
Ancestors
  guardSourceExternalPrimitives guardSourceExecution vyperCallStorageFootprint
  vyperTypeContractSoundness vyperTypeCallStackSoundness vyperTypeBindArguments
  vyperTypeContractGetter vyperTypeInitialState vyperTypeInvariants
  vyperTypeExprSoundness vyperTypeEvalStoragePreservation vyperGetter
  vyperFiniteStoragePreservation vyperTypeExternalDefaults
  vyperInterpreter vyperState vyperContext vyperStorageFootprint vyperStorageTrace

val _ = Parse.hide "body";

val getter_setup = ``
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ module_allocated am.layouts tx.target src ts /\
  MEM decl ts /\ is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src``;
val getter_context = ``initial_evaluation_context am.sources am.layouts
  (empty_call_txn with target := tx.target) src``;
val selected_conditions = ``
  IS_SOME st.outcomes /\ valid_horizon cx initial_st H st.storage_trace /\
  (?sfx. selected = out.storage_trace ++ sfx) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions selected) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks selected) /\
  storage_roots_fit selected /\
  (!pre rq co sfx.
    selected = pre ++ StorageOutcome rq co :: sfx /\
    valid_horizon cx initial_st H pre /\
    storage_well_formed_on cx
      (empty_state with <|accounts := rq.cr_accounts; tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>) (FST H))``;

Theorem getter_call_evaluation_safe[local]:
  ^getter_setup ==> call_evaluation_safe (^getter_context) (int_calls_stmts body)
Proof
  strip_tac >>
  `int_calls_stmts body = []` by
    metis_tac[selected_public_getter_body_int_calls_empty] >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    fs[checked_contract_runtime_ready_def] >>
  mp_tac (INST_TYPE [alpha |-> ``:num``]
    checked_contract_call_evaluation_safe_singleton |>
    Q.INST [`cx` |-> `^getter_context`, `owner` |-> `(src,"")`,
      `layouts` |-> `am.layouts`, `mods` |-> `mods`, `art` |-> `art`, `calls` |-> `[]`]) >>
  simp[initial_evaluation_context_def, empty_call_txn_def, calls_follow_call_graph_def]
QED

Theorem getter_current_body_finite_prefix[local]:
  ^getter_setup /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ ^selected_conditions /\
  eval_stmts cx body st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\ storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >>
  `call_evaluation_safe (^getter_context) (int_calls_stmts body)` by
    (drule_all getter_call_evaluation_safe >> simp[]) >>
  drule_all checked_public_getter_post_prefix_body_setup_selected >> strip_tac >>
  `(storage_well_formed_on (^getter_context) :
      evaluation_state -> (bool # bytes32 # type_value) list -> bool) =
   storage_well_formed_on cx` by
    (rw[FUN_EQ_THM] >> irule storage_well_formed_on_target >>
     simp[initial_evaluation_context_def]) >>
  `storage_observations_ok (^getter_context) = storage_observations_ok cx` by
    (rw[FUN_EQ_THM] >> irule storage_observations_ok_target >>
     simp[initial_evaluation_context_def]) >>
  `valid_horizon (^getter_context) = valid_horizon cx` by
    (PURE_REWRITE_TAC [FUN_EQ_THM, valid_horizon_def] >>
     qpat_assum `storage_well_formed_on (^getter_context) = _`
       (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `storage_observations_ok (^getter_context) = _`
       (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  `runtime_consistent (function_entry_env art mods src External args) (^getter_context) st` by
    simp[runtime_consistent_def] >>
  `eval_stmts (^getter_context) body st = (res,out)` by metis_tac[] >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  mp_tac (SPEC_ALL (cj 2 eval_storage_finite_prefix_mutual) |>
    Q.INST [`v0` |-> `^getter_context`, `v1` |-> `body`,
      `env` |-> `function_entry_env art mods src External args`,
      `ret_ty` |-> `ret`, `env'` |-> `env_after`, `st` |-> `st`,
      `st'` |-> `out`, `res` |-> `res`, `initial_st` |-> `initial_st`,
      `selected` |-> `selected`, `H` |-> `H`]) >>
  (impl_tac >- (fs[] >> qx_genl_tac [`pre`,`rq`,`co`,`suffix`] >> strip_tac >>
    qpat_x_assum `!pre rq co sfx. _`
      (qspecl_then [`pre`,`rq`,`co`,`suffix`] mp_tac) >>
    simp[])) >> fs[]
QED

Theorem getter_locked_body_finite_prefix[local]:
  ^getter_setup /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ ^selected_conditions /\
  (do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od) st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\ storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >> qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) st = (lr,ls)` >> Cases_on `lr` >>
  simp_tac bool_ss [pairTheory.pair_case_def, sumTheory.sum_case_def] >> strip_tac
  >- (`?tail. selected = ls.storage_trace ++ tail` by
       (mp_tac (cj 2 evaluate_storage_trace_frame) >>
        disch_then (qspecl_then [`cx`,`body`] assume_tac) >>
        drule_all storage_trace_frame_prefix >> strip_tac >>
        metis_tac[listTheory.APPEND_ASSOC]) >>
      `storage_well_formed_on cx ls (FST H) /\ storage_observations_ok cx H ls.storage_trace` by
       (`storage_observations_ok cx H st.storage_trace` by fs[valid_horizon_def] >>
        drule_at (Pat `lock_if_nr _ _ _ _ = _`) lock_if_nr_finite_prefix >>
        disch_then (qspecl_then [`selected`,`H`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> (fn g =>
          if is_exists (snd g) then
            (qexists_tac `tail` >> first_assum ACCEPT_TAC) g
          else first_assum ACCEPT_TAC g))) >> simp[]) >>
      `ls.scopes = st.scopes /\ ls.immutables = st.immutables /\ ls.accounts = st.accounts` by
       (qpat_x_assum `lock_if_nr _ _ _ _ = _` mp_tac >>
        simp[lock_if_nr_def, is_view_mut_def] >> metis_tac[call_lock_action_frame_c53]) >>
      `state_well_typed ls /\ accounts_well_typed ls.accounts` by
        (qpat_assum `state_well_typed st` mp_tac >>
         qpat_assum `accounts_well_typed st.accounts` mp_tac >>
         qpat_assum `ls.scopes = st.scopes` mp_tac >>
         qpat_assum `ls.immutables = st.immutables` mp_tac >>
         qpat_assum `ls.accounts = st.accounts` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[state_well_typed_def]) >>
      `ls.scopes = [scope] /\ ls.immutables = am.immutables` by fs[] >>
      `IS_SOME ls.outcomes` by metis_tac[optional_lock_outcomes] >>
      `valid_horizon cx initial_st H ls.storage_trace` by fs[valid_horizon_def] >>
      `?sfx. selected = out.storage_trace ++ sfx` by metis_tac[] >>
      mp_tac (SPEC_ALL getter_current_body_finite_prefix |>
        Q.INST [`st` |-> `ls`]) >>
      (impl_tac >- (rpt conj_tac >> (fn g =>
        if is_exists (snd g) then
          (qexists_tac `sfx` >> first_assum ACCEPT_TAC) g
        else first_assum ACCEPT_TAC g))) >> simp[]) >>
  qpat_x_assum `(_,_) = (_,_)`
    (SUBST_ALL_TAC o SYM o CONJUNCT2 o PURE_REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  `storage_observations_ok cx H st.storage_trace` by fs[valid_horizon_def] >>
  drule_at (Pat `lock_if_nr _ _ _ _ = _`) lock_if_nr_finite_prefix >>
  disch_then (qspecl_then [`selected`,`H`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (fn g =>
    if is_exists (snd g) then
      (qexists_tac `sfx` >> first_assum ACCEPT_TAC) g
    else first_assum ACCEPT_TAC g))) >> simp[]
QED

Theorem getter_entry_finite_prefix[local]:
  ^(inst [alpha |-> ``:expr``] getter_setup) /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  st.immutables = am.immutables /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\ ^selected_conditions /\
  (do send_call_value mut cx;
      dvs <- eval_external_defaults cx (DROP k dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do set_scopes [scope]; lock_if_nr cx nr (is_view_mut mut);
                         eval_stmts cx body od
   od) st = (res,out) ==>
  storage_well_formed_on cx out (FST H) /\ storage_observations_ok cx H out.storage_trace
Proof
  strip_tac >>
  `mut = View /\ dflts = []` by
    (Cases_on `decl` >> gvs[external_getter_tuple_def]
     >- (rename1 `VariableDecl vis _ _ _ _` >> Cases_on `vis` >>
         gvs[external_getter_tuple_def, getter_def, pairTheory.UNCURRY, AllCaseEqs()]) >>
     rename1 `HashMapDecl vis _ _ _ _ _` >> Cases_on `vis` >>
     gvs[external_getter_tuple_def, getter_def, pairTheory.UNCURRY, AllCaseEqs()]) >>
  qpat_x_assum `ignore_bind _ _ st = _` mp_tac >>
  Cases_on `cx.txn.value = 0` >>
  simp[send_call_value_def, eval_external_defaults_nil, bind_def, ignore_bind_def,
       return_def, raise_def, check_def, assert_def]
  >- (Cases_on `bind_arguments (type_env_all_modules mods) args vals` >>
      simp[raise_def, set_scopes_def, bind_def, ignore_bind_def, return_def] >> strip_tac
      >- (gvs[] >> fs[valid_horizon_def]) >>
      rename1 `bind_arguments _ _ _ = SOME scope` >>
      `scope_well_typed scope` by metis_tac[bind_arguments_scope_well_typed_from_success] >>
      `state_well_typed (st with scopes := [scope])` by fs[state_well_typed_def] >>
      `storage_well_formed_on cx (st with scopes := [scope]) (FST H)` by
        simp[storage_well_formed_on_scopes] >>
      `(st with scopes := [scope]).scopes = [scope] /\
       (st with scopes := [scope]).immutables = am.immutables /\
       accounts_well_typed (st with scopes := [scope]).accounts /\
       IS_SOME (st with scopes := [scope]).outcomes /\
       valid_horizon cx initial_st H (st with scopes := [scope]).storage_trace` by
        (simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `(do lock_if_nr cx nr (is_view_mut mut); eval_stmts cx body od)
         (st with scopes := [scope]) = (res,out)` by fs[bind_def, ignore_bind_def] >>
      `?sfx. selected = out.storage_trace ++ sfx` by metis_tac[] >>
      mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:expr``]
        getter_locked_body_finite_prefix) |>
        Q.INST [`st` |-> `st with scopes := [scope]`]) >>
      (impl_tac >- (rpt conj_tac >> (fn g =>
        if is_exists (snd g) then
          (qexists_tac `sfx` >> first_assum ACCEPT_TAC) g
        else first_assum ACCEPT_TAC g))) >> strip_tac >>
      qpat_assum `cx = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> gvs[bind_def, ignore_bind_def, assert_def, raise_def, return_def] >>
  fs[valid_horizon_def]
QED

Theorem selected_getter_finite_prefix:
  ^(inst [alpha |-> ``:expr``] getter_setup) /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx (initial_state am []) (FST H) /\
  EVERY (\r. MEM r (FST H)) (storage_trace_regions obs) /\
  EVERY (\l. MEM l (SND H)) (storage_trace_locks obs) /\ storage_roots_fit obs /\
  (!pre rq co sfx.
    obs = pre ++ StorageOutcome rq co :: sfx /\
    valid_horizon cx (initial_state am []) H pre /\
    storage_well_formed_on cx
      (empty_state with <|accounts := rq.cr_accounts; tStorage := rq.cr_tStorage|>) (FST H) ==>
    storage_well_formed_on cx
      (empty_state with <|accounts := co.co_accounts; tStorage := co.co_tStorage|>) (FST H)) /\
  call_external_function_trace (SOME os) gs am cx nr mut ts mods args dflts vals body ret =
    (res,am',rqs,obs) ==> storage_observations_ok cx H obs
Proof
  strip_tac >> `~cx.in_deploy` by simp[initial_evaluation_context_def] >>
  drule_at (Pat `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    external_function_trace_observations >> disch_then irule >> asm_rewrite_tac[] >>
  qabbrev_tac `st0 = initial_state am [FEMPTY] with
    <|outcomes := SOME os; requests := []; gas_obs := gs; storage_trace := []|>` >>
  qpat_assum `Abbrev (st0 = _)`
    (fn th => rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  rpt gen_tac >> strip_tac >>
  `state_well_typed st0 /\ accounts_well_typed st0.accounts` by
    (qpat_x_assum `machine_well_typed am` mp_tac >>
     simp[Abbr `st0`, initial_state_def, state_well_typed_def,
          machine_well_typed_def, scope_well_typed_def]) >>
  `storage_well_formed_on cx st0 (FST H)` by
    (`storage_well_formed_on cx st0 (FST H) <=>
      storage_well_formed_on cx (initial_state am []) (FST H)` by
       (irule storage_well_formed_on_backends >> simp[Abbr `st0`, initial_state_def]) >>
     metis_tac[]) >>
  `IS_SOME st0.outcomes` by simp[Abbr `st0`] >>
  `st0.immutables = am.immutables` by simp[Abbr `st0`, initial_state_def] >>
  `valid_horizon cx (initial_state am []) H st0.storage_trace` by
    simp[Abbr `st0`, valid_horizon_def, storage_observations_ok_def,
         storage_trace_regions_def, storage_trace_locks_def, storage_roots_fit_def,
         storage_trace_backends_well_formed_def] >>
  `?sfx. obs = rt.storage_trace ++ sfx` by metis_tac[] >>
  qpat_assum `cx = _` (fn th =>
    qpat_x_assum `ignore_bind _ _ st0 = _` (assume_tac o REWRITE_RULE [GSYM th])) >>
  mp_tac (SPEC_ALL getter_entry_finite_prefix |>
    Q.INST [`st` |-> `st0`, `out` |-> `rt`, `res` |-> `rr`,
      `selected` |-> `obs`, `initial_st` |-> `initial_state am []`,
      `k` |-> `LENGTH dflts - (LENGTH args - LENGTH vals)`]) >>
  (impl_tac >- (rpt conj_tac >> (fn g =>
    if is_exists (snd g) then
      (qexists_tac `sfx` >> first_assum ACCEPT_TAC) g
    else first_assum ACCEPT_TAC g))) >> strip_tac >>
  qpat_assum `cx = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  first_assum ACCEPT_TAC
QED
