(*
 * Reusable input/setup readiness predicates for checked external entry.
 *
 * TOP-LEVEL:
 * - deployment_constants_output_typed
 * - checked_deployment_constants_ready
 * - provided_args_typed
 * - checked_defaults_ready
 * - checked_call_inputs_ready
 * - checked_deployment_constants_ready_setup
 *)

Theory vyperTypeEntryReadiness
Ancestors
  list rich_list finite_map option pair
  vyperAST vyperValue vyperTyping vyperState vyperInterpreter vyperContext
  vyperTypeSystem vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeInitialState vyperTypeEvalSoundness vyperTypeExprResult vyperTypeValues

(* ===== Deployment Constant Readiness ===== *)

(* Every declared deployment constant is present in the resulting machine with
 * its evaluated declared type and a value of that type. *)
Definition deployment_constants_output_typed_def:
  deployment_constants_output_typed tenv addr mods (am:abstract_machine) <=>
    !src ts vis e id ty init.
      MEM (src,ts) mods /\
      MEM (VariableDecl vis (Constant e) id ty init) ts ==>
      ?tv v.
        FLOOKUP
          (get_source_immutables src
            (case ALOOKUP am.immutables addr of
             | SOME imms => imms
             | NONE => []))
          (string_to_num id) = SOME (tv,v) /\
        evaluate_type tenv ty = SOME tv /\
        value_has_type tv v
End

(* Setup readiness is invocation-specific.  It records both that deployment
 * constant evaluation succeeds and that every successful output has the
 * public output-typing property above. *)
Definition checked_deployment_constants_ready_def:
  checked_deployment_constants_ready cx am addr mods <=>
    IS_SOME (evaluate_all_constants cx am addr mods) /\
    !am_c.
      evaluate_all_constants cx am addr mods = SOME am_c ==>
      deployment_constants_output_typed (get_tenv cx) addr mods am_c
End

Theorem checked_deployment_constants_ready_setup:
  checked_deployment_constants_ready cx am addr mods ==>
  ?am_c.
    evaluate_all_constants cx am addr mods = SOME am_c /\
    deployment_constants_output_typed (get_tenv cx) addr mods am_c
Proof
  rw[checked_deployment_constants_ready_def, IS_SOME_EXISTS] >>
  metis_tac[]
QED

(* ===== Default and Argument Readiness ===== *)

(* The externally supplied values type-check against the corresponding prefix
 * of the selected function's parameter list. *)
Definition provided_args_typed_def:
  provided_args_typed tenv (args:argument list) vals <=>
    args_values_typed tenv (TAKE (LENGTH vals) args) vals
End

(* The selected default suffix exists and evaluates successfully.  Typing of
 * its successful result is derived from checked-function expression soundness,
 * rather than included as an input premise. *)
Definition checked_defaults_ready_def:
  checked_defaults_ready cx am (args:argument list) dflts vals <=>
    LENGTH vals <= LENGTH args /\
    LENGTH args - LENGTH vals <= LENGTH dflts /\
    IS_SOME
      (evaluate_defaults cx am
        (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts))
End

Definition checked_call_inputs_ready_def:
  checked_call_inputs_ready tenv cx am args dflts vals <=>
    provided_args_typed tenv args vals /\
    checked_defaults_ready cx am args dflts vals
End

(* Successful evaluation of a well-typed default list returns values of the
 * defaults' expression types.  Each default is evaluated from the same entry
 * machine state by evaluate_defaults. *)
Theorem evaluate_defaults_success_values_typed:
  well_typed_exprs env es /\
  env_consistent env cx (initial_state am []) /\
  state_well_typed (initial_state am []) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  (!e. MEM e es ==> call_evaluation_safe cx (int_calls_expr e)) /\
  evaluate_defaults cx am es = SOME vs ==>
  LIST_REL
    (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                  value_has_type tv v)
    vs es
Proof
  qid_spec_tac `vs` >> Induct_on `es`
  >- simp[evaluate_defaults_def] >>
  gen_tac >> rpt strip_tac >>
  gvs[well_typed_expr_def, evaluate_defaults_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx h (initial_state am [])` >> gvs[] >>
  `accounts_well_typed (initial_state am []).accounts` by
    simp[initial_state_def] >>
  `call_evaluation_safe cx (int_calls_expr h)` by metis_tac[] >>
  drule_all (cj 8 eval_all_type_sound_mutual) >>
  simp[expr_result_typed_def, expr_runtime_typed_def,
       toplevel_value_typed_Value]
QED

Theorem checked_defaults_ready_success:
  checked_defaults_ready cx am args dflts vals ==>
  LENGTH vals <= LENGTH args /\
  LENGTH args - LENGTH vals <= LENGTH dflts /\
  ?dflt_vs.
    evaluate_defaults cx am
      (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) =
      SOME dflt_vs
Proof
  rw[checked_defaults_ready_def, IS_SOME_EXISTS]
QED

Theorem checked_defaults_ready_values_typed:
  checked_defaults_ready cx am args dflts vals /\
  well_typed_exprs env
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) /\
  env_consistent env cx (initial_state am []) /\
  state_well_typed (initial_state am []) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  (!e.
    MEM e (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) ==>
    call_evaluation_safe cx (int_calls_expr e)) ==>
  ?dflt_vs.
    evaluate_defaults cx am
      (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) =
      SOME dflt_vs /\
    LIST_REL
      (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                    value_has_type tv v)
      dflt_vs
      (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts)
Proof
  rw[checked_defaults_ready_def, IS_SOME_EXISTS] >>
  `LENGTH dflts - (LENGTH args - LENGTH vals) =
   LENGTH vals + LENGTH dflts - LENGTH args` by decide_tac >>
  gvs[] >>
  drule_all evaluate_defaults_success_values_typed >> simp[]
QED

Theorem checked_call_inputs_ready_components:
  checked_call_inputs_ready tenv cx am args dflts vals ==>
  provided_args_typed tenv args vals /\
  checked_defaults_ready cx am args dflts vals
Proof
  simp[checked_call_inputs_ready_def]
QED

