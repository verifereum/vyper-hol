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
  vyperTypeSystem vyperTypeInitialState

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

Theorem checked_call_inputs_ready_components:
  checked_call_inputs_ready tenv cx am args dflts vals ==>
  provided_args_typed tenv args vals /\
  checked_defaults_ready cx am args dflts vals
Proof
  simp[checked_call_inputs_ready_def]
QED

