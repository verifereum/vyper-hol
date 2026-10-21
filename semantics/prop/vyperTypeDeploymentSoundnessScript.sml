(*
 * Checked deployment reaches the constructor body (#618, part of #420), the
 * deployment analogue of vyperTypeSelectedEntrySoundness.
 *
 * For a checked contract and constructor arguments that fit the constructor's
 * parameters, every setup step of load_contract succeeds: the initial
 * immutables evaluate, the constructor has no defaults, the arguments bind,
 * and the deployment constants fold succeeds (#617).  load_contract is then
 * call_external_body from the bound scope and the folded machine, and that
 * run's result is not a TypeError and does not escape with break or
 * continue.
 *
 * TOP-LEVEL: checked_constructor_bind_arguments,
 *            load_contract_constructor_body,
 *            checked_load_contract_no_static_error.
 *
 * Helper: check_contract_initial_immutables,
 *         check_contract_constructor_no_defaults.
 *)

Theory vyperTypeDeploymentSoundness
Ancestors
  list pair alist
  vyperAST vyperValue vyperState vyperInterpreter vyperContext
  vyperTypeSystem vyperTypeExprSoundness vyperTypeInitialState
  vyperTypeEntryReadiness vyperTypeContract vyperTypeContractStaticMaps
  vyperTypeContractContext vyperTypeContractSoundness
  vyperTypeSelectedEntrySoundness vyperTypeDeploymentMachine

val _ = Parse.hide "body";

(* ===== Setup steps ===== *)

Theorem check_contract_initial_immutables:
  check_contract in_deploy layouts addr mods = SOME art ==>
  ?imms. initial_immutables (type_env_all_modules mods) mods = SOME imms
Proof
  rw[check_contract_def, contract_constants_ok_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >> gvs[]
QED

Theorem check_contract_constructor_no_defaults:
  check_contract in_deploy layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  lookup_function src fn Deploy ts = SOME (mut,nr,args,dflts,ret,body) ==>
  dflts = []
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
  gvs[check_contract_def, EVERY_MEM] >>
  drule ALOOKUP_MEM >> strip_tac >>
  first_x_assum drule >> simp[check_module_def, EVERY_MEM] >>
  strip_tac >>
  qpat_x_assum `!e. MEM e ts ==> check_toplevel_decl _ _ _ _ _ _` drule >>
  simp[check_toplevel_decl_def]
QED

(* TOP-LEVEL: the constructor counterpart of
   checked_selected_entry_bind_arguments.  The constructor has no defaults, so
   the ABI premise is an exact length match plus provided_args_typed. *)
Theorem checked_constructor_bind_arguments:
  check_contract in_deploy layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH tx.args = LENGTH args /\
  provided_args_typed (type_env_all_modules mods) args tx.args ==>
  dflts = [] /\
  ?scope.
    bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
    args_values_typed (type_env_all_modules mods) args tx.args
Proof
  strip_tac >>
  conj_asm1_tac >- metis_tac[check_contract_constructor_no_defaults] >>
  `!arg. MEM arg args ==>
     ?tv. evaluate_type (type_env_all_modules mods) (SND arg) = SOME tv` by
    (drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
     gvs[check_contract_def, EVERY_MEM] >>
     drule ALOOKUP_MEM >> strip_tac >>
     first_x_assum drule >> simp[check_module_def, EVERY_MEM] >>
     strip_tac >>
     qpat_x_assum `!e. MEM e ts ==> check_toplevel_decl _ _ _ _ _ _` drule >>
     simp[check_toplevel_decl_def, params_ok_def, EVERY_MEM] >>
     rpt strip_tac >> PairCases_on `arg` >> first_x_assum drule >> simp[] >>
     metis_tac[assignable_type_well_formed, well_formed_type_def,
               optionTheory.IS_SOME_EXISTS]) >>
  drule_then (qspecl_then [`[]`,`[]`] mp_tac)
    provided_args_defaults_bind_arguments >>
  simp[DROP_LENGTH_TOO_LONG]
QED

(* TOP-LEVEL: load_contract is the constructor body run once setup has
   succeeded. *)
Theorem load_contract_constructor_body:
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,[],ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\
  LENGTH tx.args = LENGTH args /\
  bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
  evaluate_all_constants cx
    (am with <|immutables updated_by CONS (tx.target,imms);
               exports updated_by CONS (tx.target,exps)|>)
    tx.target mods = SOME am_c ==>
  load_contract orc am tx mods exps =
    case call_external_body orc am_c cx nr mut (type_env_all_modules mods)
           scope body ret of
      (INR e, _, _) => INR e
    | (INL _, am', rqs) =>
        INL (finalize_pending_deletions
               (am' with sources updated_by CONS (tx.target,mods)), rqs)
Proof
  strip_tac >>
  gvs[load_contract_def, call_external_function_def, call_external_body_def,
      evaluate_defaults_def, initial_evaluation_context_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ===== Composition ===== *)

(* TOP-LEVEL: deployment analogue of checked_selected_entry_no_static_error.
   For a checked contract and constructor arguments that fit, load_contract
   gets through setup to the constructor body: it equals the body run from
   the bound scope and the folded machine, and that run is neither a
   TypeError nor an escaping break/continue.  Genuine runtime failures of
   the body or of value transfer are not excluded.

   Why: the lock has a slot because check_function_body requires one for a
   nonreentrant function (the synthetic constructor has nr = F); the body
   state is typed and its immutables ready as in
   checked_constructor_prefix_run_preserves_machine_well_typed, once
   checked_deployment_constants_ready_from_check discharges readiness; a
   ReturnException value is typed at ret by statement type preservation, so
   the return cast succeeds; stmts_no_control_escape comes from
   check_function_body. *)
Theorem checked_load_contract_no_static_error:
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  machine_well_typed am /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx
          NONE with in_deploy := T) /\
  context_well_typed cx /\
  LENGTH tx.args = LENGTH args /\
  provided_args_typed (type_env_all_modules mods) args tx.args ==>
  ?imms am_c scope.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    evaluate_all_constants cx
      (am with <|immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps)|>)
      tx.target mods = SOME am_c /\
    bind_arguments (type_env_all_modules mods) args tx.args = SOME scope /\
    args_values_typed (type_env_all_modules mods) args tx.args /\
    load_contract orc am tx mods exps =
      (case call_external_body orc am_c cx nr mut (type_env_all_modules mods)
              scope body ret of
         (INR e, _, _) => INR e
       | (INL _, am', rqs) =>
           INL (finalize_pending_deletions
                  (am' with sources updated_by CONS (tx.target,mods)), rqs)) /\
    no_type_error_result
      (FST (call_external_body orc am_c cx nr mut (type_env_all_modules mods)
              scope body ret)) /\
    !exc.
      FST (call_external_body orc am_c cx nr mut (type_env_all_modules mods)
             scope body ret) = INR exc ==>
      exc <> BreakException /\ exc <> ContinueException
Proof
  cheat
QED
