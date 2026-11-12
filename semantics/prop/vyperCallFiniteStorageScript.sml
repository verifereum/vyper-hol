(*
 * Whole-run finite storage preservation: a checked external call, and a
 * checked constructor run, keep every region of a valid horizon in range.
 *)
Theory vyperCallFiniteStorage
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint vyperTypeSelectedEntry
  vyperTypeExternalCallMachine vyperTypeExternalDefaults
  vyperTypeDeploymentMachine vyperTypeContractSoundness vyperLookupStorage
  vyperStorage vyperStorageBackend vyperState vyperInterpreter vyperContext
  vyperCall vyperStorageTrace vyperTypeInvariants vfmState
  vyperCallFiniteStorageSupport vyperExternalDefaultsFiniteStorage
  vyperGetterFiniteStorage vyperExternalBodyFiniteStorage
  vyperExternalEntryStorageFrame vyperExplicitEntryFiniteStorage
  vyperGetterEntryFiniteStorage vyperTypeInitialState vyperTypeContractFunction
  vyperConstructorInitialReady vyperConstructorEntryFiniteStorage
  vyperConstantsStorageFrame

val _ = Parse.hide "body";

(* Intuition: storage_well_formed_on reads only cx.txn.target, so the
   NONE-module context and the selected module's context agree. Lookup and
   binding failures return am unchanged. Otherwise the body runs from a state
   with am's accounts and tStorage (the value transfer moves balances only),
   set up by checked_explicit_external_body_setup (getters likewise) or
   checked_constructor_body_setup, with call_evaluation_safe from
   checked_*_body_call_evaluation_safe; eval_storage_well_formed_on_mutual
   carries the horizon through the body, its observations being a prefix of
   obs. finalize_pending_deletions only empties accounts, and empty storage
   is in range. *)

(* Zero storage decodes on every region. *)
Theorem empty_storage_well_formed_on:
  (!b. get_storage cx st b = empty_storage) ==>
  storage_well_formed_on cx st regions
Proof
  rw[storage_well_formed_on_def] >>
  irule (CONJUNCT1 slots_in_range_zero_reads) >>
  simp[read_slot_def, lookup_storage_def, empty_storage_def]
QED

Theorem call_external_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  call_external_trace orc gobs am tx = (res,am',rqs,obs) /\
  valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H obs ==>
  storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am' []) (FST H)
Proof
  strip_tac >>
  Cases_on `?exc. res = INR exc /\ exc <> HaltException`
  >- (gvs[] >>
      `call_external orc gobs am tx = (INR exc,am',rqs)` by
        simp[call_external_def] >>
      `am' = am` by metis_tac[call_external_error_rollback] >>
      gvs[valid_horizon_def]) >>
  `?sel. selected_entry am tx mods sel` by
    (Cases_on `?ms sel. selected_entry am tx ms sel`
     >- (gvs[selected_entry_def, checked_contract_runtime_ready_def] >> metis_tac[]) >>
     drule call_external_not_selected_entry >> strip_tac >>
     `call_external orc gobs am tx = (res,am',rqs)` by simp[call_external_def] >>
     metis_tac[exception_distinct, sumTheory.INR_11, pairTheory.PAIR_EQ]) >>
  PairCases_on `sel` >>
  rename1 `selected_entry am tx mods (mut,nr,args,dflts,ret,body)` >>
  qabbrev_tac `src = find_function_module am tx.target tx.function_name` >>
  `?ts. ALOOKUP mods src = SOME ts /\
    ((?raw. MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts) \/
     (?decl. MEM decl ts /\ is_public_getter_decl tx.function_name decl /\
       external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body)))` by
    (irule selected_entry_checked_cases >> metis_tac[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `src = find_function_module am tx.target tx.function_name` by simp[Abbr `src`] >>
  `cx = initial_evaluation_context am.sources am.layouts tx src` by simp[Abbr `cx`] >>
  drule_all call_external_selected_entry_trace >>
  disch_then (qspecl_then [`orc`,`gobs`] assume_tac) >>
  qpat_x_assum `src = find_function_module _ _ _` kall_tac >>
  qpat_x_assum `cx = initial_evaluation_context _ _ _ _` kall_tac >>
  Cases_on `call_external_function_trace orc gobs am cx nr mut ts mods args dflts tx.args body ret` >>
  rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (out,p)` >>
  PairCases_on `p` >>
  rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (out,am_run,rqs_run,obs_run)` >>
  suspend "selected"
QED

Resume call_external_storage_well_formed_on[selected]:
  markerLib.RESUME_TAC >>
  `storage_well_formed_on cx (initial_state am_run []) (FST H)` suffices_by
    (strip_tac >>
     `!st (regions : (bool # bytes32 # type_value) list). storage_well_formed_on cx st regions <=>
       storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE) st regions` by
       (rpt gen_tac >> irule storage_well_formed_on_target >>
        simp[Abbr `cx`, initial_evaluation_context_def]) >>
     Cases_on `out` >> gvs[]
     >- (irule finalize_pending_deletions_preserves_storage_well_formed_on >> metis_tac[]) >>
     rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (INR exc,_)` >> Cases_on `exc` >> gvs[] >>
     irule finalize_pending_deletions_preserves_storage_well_formed_on >> metis_tac[]) >>
  `obs_run = obs` by
    (Cases_on `out` >> gvs[] >>
     rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (INR exc,_)` >>
     Cases_on `exc` >> gvs[]) >>
  `!st (regions : (bool # bytes32 # type_value) list).
    storage_well_formed_on cx st regions <=>
    storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE) st regions` by
    (rpt gen_tac >> irule storage_well_formed_on_target >>
     simp[Abbr `cx`, initial_evaluation_context_def]) >>
  `storage_observations_ok cx H obs` by
    (`storage_observations_ok cx H obs <=> storage_observations_ok
       (initial_evaluation_context am.sources am.layouts tx NONE) H obs` by
       (irule storage_observations_ok_target >> simp[Abbr `cx`, initial_evaluation_context_def]) >>
     fs[valid_horizon_def]) >>
  `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
   storage_well_formed_on cx (initial_state am []) (FST H)` by
    (fs[valid_horizon_def] >> metis_tac[]) >>
  `module_allocated am.layouts tx.target src ts` by
    (simp[Abbr `src`] >> irule checked_contract_runtime_ready_module_allocated >>
     metis_tac[]) >>
  `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  drule_at (Pat `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    call_external_function_trace_storage_well_formed_on >>
  disch_then (qspec_then `H` mp_tac) >>
  simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  disch_then irule >> rpt gen_tac >> strip_tac >>
  `storage_well_formed_on cx u (FST H)` suffices_by metis_tac[] >>
  qpat_x_assum `!st regions. _` kall_tac >>
  `storage_well_formed_on cx
    (initial_state am [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >>
     goal_assum (drule_at Any) >> simp[initial_state_def])
  >>~- ([`MEM (FunctionDecl External _ _ _ _ _ _ _ _) _`], suspend "explicit") >>
  suspend "getter"
QED

Resume call_external_storage_well_formed_on[explicit]:
  `context_well_typed cx` by
    (fs[Abbr `cx`, call_tx_well_typed_def, context_well_typed_def,
        initial_evaluation_context_def]) >>
  `state_well_typed
    (initial_state am [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>) /\
   accounts_well_typed am.accounts` by
    fs[machine_well_typed_def, initial_state_def, state_well_typed_def,
       scope_well_typed_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (fs[checked_contract_runtime_ready_def, Abbr `cx`] >>
     irule immutables_ready_initial_evaluation_context_source >> simp[]) >>
  `ALOOKUP am.sources tx.target = SOME mods` by fs[checked_contract_runtime_ready_def] >>
  `!s r t. storage_well_formed_on cx s (FST H) /\
     storage_observations_ok cx H t.storage_trace /\
     send_call_value mut cx s = (r,t) ==>
     storage_well_formed_on cx t (FST H)` by
    metis_tac[send_call_value_preserves_storage_well_formed_on] >>
  `!s r t. storage_well_formed_on cx s (FST H) /\
     storage_observations_ok cx H t.storage_trace /\
     lock_if_nr cx nr (is_view_mut mut) s = (r,t) ==>
     storage_well_formed_on cx t (FST H)` by
    metis_tac[lock_if_nr_preserves_storage_well_formed_on] >>
  `cx = initial_evaluation_context am.sources am.layouts tx src` by simp[Abbr `cx`] >>
  `accounts_well_typed (initial_state am [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>).accounts /\
   immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx
     (initial_state am [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>).immutables` by
    (simp_tac (srw_ss()) [initial_state_def] >> metis_tac[]) >>
  drule_all checked_explicit_entry_storage_well_formed_on >> simp_tac bool_ss []
QED

Resume call_external_storage_well_formed_on[getter]:
  `cx = initial_evaluation_context am.sources am.layouts tx src` by simp[Abbr `cx`] >>
  metis_tac[checked_getter_entry_storage_well_formed_on]
QED

Finalise call_external_storage_well_formed_on

Theorem load_contract_storage_well_formed_on:
  machine_well_typed am /\
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  context_well_typed
    (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
       (tx with created_in_tx := T) NONE with in_deploy := T) /\
  load_contract_trace orc gobs am tx mods exps = (INL (am',rqs),obs) /\
  valid_horizon
    (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
       (tx with created_in_tx := T) NONE with in_deploy := T)
    (initial_state am []) H obs ==>
  storage_well_formed_on
    (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
       (tx with created_in_tx := T) NONE with in_deploy := T)
    (initial_state am' []) (FST H)
Proof
  strip_tac >>
  qabbrev_tac `cx = (initial_evaluation_context ((tx.target,mods)::am.sources)
    am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)` >>
  qpat_x_assum `load_contract_trace _ _ _ _ _ _ = _` mp_tac >>
  simp[Once load_contract_trace_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >> simp[] >>
  rename1 `initial_immutables _ _ = SOME imms` >>
  Cases_on `lookup_function NONE tx.function_name Deploy
    (case ALOOKUP mods NONE of NONE => [] | SOME ts => ts)` >> simp[] >>
  PairCases_on `x` >>
  rename1 `lookup_function _ _ _ _ = SOME (mut,nr,args,dflts,ret,body)` >>
  simp_tac std_ss [] >>
  Cases_on `call_external_function_trace orc gobs
    (am with <|exports updated_by CONS (tx.target,exps);
      immutables updated_by CONS (tx.target,imms)|>) cx nr mut
    (case ALOOKUP mods NONE of NONE => [] | SOME ts => ts)
    mods args dflts tx.args body ret` >>
  rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (out,p)` >>
  PairCases_on `p` >>
  rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (out,am_run,rqs_run,obs_run)` >>
  strip_tac >>
  `obs_run = obs` by (Cases_on `out` >> gvs[] >>
    rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (INR exc,_)` >>
    Cases_on `exc` >> gvs[]) >>
  `storage_well_formed_on cx (initial_state am_run []) (FST H)` suffices_by
    (strip_tac >> Cases_on `out` >> gvs[]
     >- (irule finalize_pending_deletions_preserves_storage_well_formed_on >>
         irule (iffRL storage_well_formed_on_backends) >>
         goal_assum (drule_at Any) >> simp[initial_state_def]) >>
     rename1 `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = (INR exc,_)` >>
     Cases_on `exc` >> gvs[] >>
     irule finalize_pending_deletions_preserves_storage_well_formed_on >> simp[]) >>
  drule_at (Pat `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    call_external_function_trace_storage_well_formed_on_general >>
  disch_then (qspec_then `H` mp_tac) >>
  simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  impl_tac >- suspend "initial_and_entry" >> simp[]
QED

Resume load_contract_storage_well_formed_on[initial_and_entry]:
  `regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
   storage_well_formed_on cx (initial_state am []) (FST H) /\
   storage_observations_ok cx H obs` by fs[valid_horizon_def] >>
  `storage_well_formed_on cx (initial_state
     (am with <|exports updated_by CONS (tx.target,exps);
       immutables updated_by CONS (tx.target,imms)|>) []) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >>
     goal_assum (drule_at Any) >> simp[initial_state_def]) >>
  ASM_SIMP_TAC bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  `cx.in_deploy /\ cx.txn.target = tx.target` by
    simp[Abbr `cx`, initial_evaluation_context_def] >>
  `evaluate_all_constants cx
     (am with <|exports updated_by CONS (tx.target,exps);
       immutables updated_by CONS (tx.target,imms)|>) tx.target mods = SOME am_c` by
    (simp[evaluate_all_constants_def, evaluate_module_constants_def] >>
     gvs[]) >>
  `machine_well_typed (am with <|exports updated_by CONS (tx.target,exps);
     immutables updated_by CONS (tx.target,imms)|>)` by
    (drule_all deployment_initial_machine_well_typed >>
     disch_then (qspecl_then [`exps`,`tx.target`] mp_tac) >> simp[]) >>
  `checked_deployment_constants_ready cx
    (am with <|exports updated_by CONS (tx.target,exps);
       immutables updated_by CONS (tx.target,imms)|>) tx.target mods` by
    (metis_tac[SRULE [] checked_constructor_constants_ready]) >>
  `cx = (initial_evaluation_context ((tx.target,mods)::am.sources)
    am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)` by
    simp[Abbr `cx`] >>
  `ALOOKUP ((tx.target,mods)::am.sources) tx.target = SOME mods /\
   (tx with created_in_tx := T).target = tx.target` by simp[] >>
  `state_well_typed (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := constant_trace|>) /\
   accounts_well_typed am_c.accounts /\
   env_immutables_consistent (artifact_env deploy_art mods NONE) cx
     (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := constant_trace|>)` by
    (irule checked_constructor_initial_state_ready >>
     qexistsl [`am with exports updated_by CONS (tx.target,exps)`,`imms`,
       `am.layouts`,`runtime_art`,`(tx.target,mods)::am.sources`,`tx.target`,
       `tx with created_in_tx := T`] >> simp[NoAsms] >> metis_tac[]) >>
  `am_c.accounts = am.accounts /\ am_c.tStorage = am.tStorage` by
    (drule evaluate_all_constants_machine_frame >>
     disch_then (mp_tac o Q.AP_TERM `\m. (m.accounts,m.tStorage)`) >> simp[]) >>
  `storage_well_formed_on cx (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := constant_trace|>) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >>
     qexists `initial_state am []` >> simp[initial_state_def]) >>
  Cases_on `ALOOKUP mods NONE`
  >- suspend "synthetic" >>
  rename1 `ALOOKUP mods NONE = SOME ts` >>
  `lookup_function NONE (tx with created_in_tx := T).function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body)` by
    (qpat_x_assum `lookup_function _ _ _ _ = _` mp_tac >> simp[NoAsms]) >>
  `check_contract T am.layouts (tx with created_in_tx := T).target mods = SOME deploy_art /\
   check_contract F am.layouts (tx with created_in_tx := T).target mods = SOME runtime_art` by simp[] >>
  `accounts_well_typed (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := constant_trace|>).accounts` by
    (simp[NoAsms, initial_state_def] >> metis_tac[]) >>
  metis_tac[checked_constructor_entry_storage_well_formed_on]
QED

Resume load_contract_storage_well_formed_on[synthetic]:
  qpat_x_assum `lookup_function _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [lookup_function_def] >>
  strip_tac >>
  map_every (fn q => qpat_x_assum q SUBST_ALL_TAC)
    [`mut = Payable`, `args = []`, `dflts = []`, `ret = NoneT`, `body = []`] >>
  qpat_x_assum `~nr` (SUBST_ALL_TAC o EQF_INTRO) >>
  qpat_x_assum `ignore_bind _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [eval_external_defaults_nil, bind_arguments_def,
    lock_if_nr_def, evaluate_def, bind_def, ignore_bind_def,
    set_scopes_def, return_def] >>
  qmatch_goalsub_abbrev_tac `send_call_value Payable cx st` >>
  Cases_on `send_call_value Payable cx st` >>
  rename1 `send_call_value Payable cx st = (sr,ss)` >>
  `storage_well_formed_on cx ss (FST H)` by
    (irule send_call_value_preserves_storage_well_formed_on >>
     goal_assum (drule_at Any) >> simp_tac bool_ss [Abbr `st`] >> metis_tac[]) >>
  Cases_on `sr` >> simp_tac (srw_ss()) []
  >- (Cases_on `bind_arguments (type_env_all_modules mods) [] tx.args` >>
      simp_tac (srw_ss()) [raise_def, bind_def, set_scopes_def, return_def] >>
      strip_tac >>
      qpat_x_assum `_ = u` (SUBST_ALL_TAC o SYM) >>
      irule (iffRL storage_well_formed_on_backends) >>
      qexists `ss` >> simp[]) >>
  strip_tac >> metis_tac[pairTheory.PAIR_EQ]
QED

Finalise load_contract_storage_well_formed_on
