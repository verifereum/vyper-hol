(*
 * Pass Simulation Framework — Definitions
 *
 * Generic block→function lifting for pass correctness proofs,
 * parameterized by dual state relations (R_ok, R_term).
 *
 * R_ok governs OK results (execution continues — needs control flow match).
 * R_term governs Halt/Revert results (terminal — control flow irrelevant).
 *
 * Instantiations:
 *   result_equiv vars = lift_result (state_equiv vars) (execution_equiv vars)
 *   uniform R         = lift_result R R
 *
 * TOP-LEVEL:
 *   block_map_transform      — MAP f over block instructions
 *   function_map_transform   — MAP bt over function blocks
 *   inst_simulates           — per-instruction simulation predicate
 *   block_simulates          — whole-block simulation predicate
 *   terminates               — execution terminates (not Error)
 *   pass_correct             — combined termination + result equivalence
 *)

Theory passSimulationDefs
Ancestors
  stateEquiv venomExecSemantics venomInst

(* ===== Transform definitions ===== *)

(* Level 1: 1:1 instruction mapping *)
Definition block_map_transform_def:
  block_map_transform f bb =
    bb with bb_instructions := MAP f bb.bb_instructions
End

(* Function transform: apply block transform to all blocks *)
Definition function_map_transform_def:
  function_map_transform bt fn =
    fn with fn_blocks := MAP bt fn.fn_blocks
End

(* ===== Simulation predicates ===== *)

(* Level 1: per-instruction simulation.
   f preserves lift_result for every instruction and state,
   and preserves the is_terminator property. *)
Definition inst_simulates_def:
  inst_simulates R_ok R_term f <=>
    (!inst s.
       lift_result R_ok R_term (step_inst inst s) (step_inst (f inst) s)) /\
    (!inst. is_terminator inst.inst_opcode =
            is_terminator (f inst).inst_opcode)
End

(* Level 2: whole-block simulation.
   Running the transformed block gives a related result. *)
Definition block_simulates_def:
  block_simulates R_ok R_term bt <=>
    !bb s.
      lift_result R_ok R_term (run_block bb s) (run_block (bt bb) s)
End

(* ===== Pass correctness predicates ===== *)

(* Execution terminates (not Error). *)
Definition terminates_def:
  terminates r <=> case r of Error _ => F | _ => T
End

(* Two executions (parameterized by fuel) are pass-correct:
   1. Termination equivalence: original terminates iff transformed terminates
   2. Result equivalence: when both terminate, results are equivalent
      (modulo fresh variables introduced by the transformation)
   Usage: pass_correct fresh (\fuel. run_function fuel fn s)
                              (\fuel. run_function fuel fn' s) *)
Definition pass_correct_def:
  pass_correct fresh exec1 exec2 <=>
    ((?fuel. terminates (exec1 fuel)) <=> (?fuel'. terminates (exec2 fuel'))) /\
    (!fuel fuel'.
       terminates (exec1 fuel) /\ terminates (exec2 fuel') ==>
       result_equiv fresh (exec1 fuel) (exec2 fuel'))
End
