(* Storage preservation for the generated-getter entry computation. *)
Theory vyperGetterEntryFiniteStorage
Ancestors
  vyperGetterFiniteStorage vyperReadOnlySyntax vyperTypeContractSoundness
  vyperInterpreter vyperContext vyperState vyperStorageFootprint
  vyperTypeContractGetter vyperGetter vyperTypeSystem vyperTypeInvariants
  vyperTypeBindArguments vyperCallFiniteStorageSupport vyperStorageBackend vyperTypeInitialState

val _ = Parse.hide "body";

Theorem checked_getter_entry_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st = (initial_state am [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []|>) /\
  (do send_call_value mut cx;
      dflt_vs <- eval_external_defaults cx
        (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME scope => do set_scopes [scope];
                         lock_if_nr cx nr (is_view_mut mut);
                         eval_stmts cx body od
   od) st = (res,st') /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >>
  `dflts = []` by metis_tac[external_getter_defaults] >>
  `mut = View` by
    (Cases_on `decl` >> gvs[external_getter_tuple_def]
     >- (rename1 `VariableDecl vis _ _ _ _` >> Cases_on `vis` >>
         gvs[external_getter_tuple_def, getter_def, AllCaseEqs()] >>
         pairarg_tac >> gvs[]) >>
     rename1 `HashMapDecl vis _ _ _ _ _` >> Cases_on `vis` >>
     gvs[external_getter_tuple_def, getter_def] >> pairarg_tac >> gvs[]) >>
  `nr ==> cx.nonreentrant_slot <> NONE` by
    (strip_tac >> drule_all checked_selected_getter_lock_slot >>
     simp[initial_evaluation_context_def]) >>
  gvs[eval_external_defaults_nil, is_view_mut_def] >>
  qpat_x_assum `(do _; _ od) _ = _` mp_tac >>
  simp[send_call_value_def, check_def, assert_def, bind_def, ignore_bind_def,
       return_def, raise_def] >>
  reverse IF_CASES_TAC >- (simp[assert_def, bind_def, raise_def] >> strip_tac >> gvs[]) >>
  simp[return_def] >>
  Cases_on `bind_arguments (type_env_all_modules mods) args vals`
  >- (simp[raise_def] >> strip_tac >> gvs[]) >>
  rename1 `bind_arguments _ args vals = SOME scope` >>
  simp[set_scopes_def, bind_def, ignore_bind_def, return_def] >>
  strip_tac >>
  drule (INST_TYPE [``:'a`` |-> ``:unit``] view_lock_prefix_execution) >>
  disch_then (qspecl_then
    [`initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs; storage_trace := []; scopes := [scope]|>`,
     `eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body`] strip_assume_tac) >>
  gvs[ignore_bind_def, bind_def]
  >- (
  qpat_x_assum `(res,st') = eval_stmts _ _ _` (assume_tac o SYM) >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  qmatch_asmsub_abbrev_tac `eval_stmts ecx body bst` >>
  `state_well_typed bst /\ accounts_well_typed bst.accounts /\
   bst.scopes = [scope] /\ bst.immutables = am.immutables` by
    gvs[Abbr `bst`, initial_state_def, state_well_typed_def,
        machine_well_typed_def] >>
  `storage_well_formed_on ecx bst (FST H)` by
    (qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
     simp[Abbr `bst`, Abbr `ecx`, storage_well_formed_on_def, FORALL_BOOL, get_storage_def]) >>
  metis_tac[checked_public_getter_body_storage_well_formed_on]) >>
  qpat_x_assum `storage_well_formed_on _ _ _` mp_tac >>
  simp[storage_well_formed_on_def, FORALL_BOOL, get_storage_def]
QED
