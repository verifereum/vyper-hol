(* Finite-storage preservation at the checked constructor body boundary. *)
Theory vyperConstructorBodyFiniteStorage
Ancestors
  vyperTypeDeploymentMachine vyperFiniteStoragePreservation
  vyperTypeContractStaticMaps vyperTypeContractSoundness
  vyperTypeCallStackSoundness vyperTypeCallGraph vyperTypeExprSoundness
  vyperTypeSystem vyperTypeInvariants vyperInterpreter vyperContext vyperState
  vyperStorageFootprint

val _ = Parse.hide "body";

Theorem checked_constructor_body_storage_well_formed_on:
  check_contract T layouts tx.target mods = SOME deploy_art /\
  check_contract F layouts tx.target mods = SOME runtime_art /\
  ALOOKUP sources tx.target = SOME mods /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE
          with in_deploy := T) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  st.scopes = [scope] /\ state_well_typed st /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_stmts cx body st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >>
  drule_all checked_constructor_body_setup >> strip_tac >>
  `runtime_consistent env_body cx st` by
    simp[runtime_consistent_def] >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[]
     >- (`(initial_evaluation_context sources layouts tx NONE
              with in_deploy := T) =
            ((initial_evaluation_context sources layouts tx NONE
                with in_deploy := T)
               with stk := [(NONE,tx.function_name)])` by
            simp[initial_evaluation_context_def] >>
         pop_assum SUBST1_TAC >>
         irule (INST_TYPE [``:'a`` |-> ``:num``]
           checked_contract_call_evaluation_safe_singleton) >>
         qexistsl [`deploy_art`,`layouts`,`mods`] >>
         simp[initial_evaluation_context_def, calls_follow_call_graph_def]) >>
     gvs[] >> irule checked_constructor_body_call_evaluation_safe >>
     qexistsl [`args`,`deploy_art`,`dflts`,`mods`,`mut`,`nr`,`raw`,`ret`,`ts`] >>
     simp[]) >>
  irule (cj 2 (SPEC_ALL eval_storage_well_formed_on_mutual)) >>
  metis_tac[]
QED
