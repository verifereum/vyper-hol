(*
 * Pass Simulation Framework — Definitions
 *
 * Generic block→function lifting for pass correctness proofs,
 * parameterized by state relation R.
 *
 * TOP-LEVEL:
 *   lift_result                  — lift state relation R through exec_result
 *   block_map_transform       — MAP f over block instructions
 *   function_map_transform    — MAP bt over function blocks
 *   inst_simulates            — per-instruction simulation predicate (param by R)
 *   block_simulates           — whole-block simulation predicate (param by R)
 *)

Theory passSimulationDefs
Ancestors
  stateEquiv execEquiv venomSem venomInst

(* ===== Result relation ===== *)

(* Lift state relation R through exec_result.
   result_equiv = lift_result state_equiv
   result_equiv_except fresh = lift_result (state_equiv_except fresh) *)
Definition lift_result_def:
  lift_result R (OK s1) (OK s2) = R s1 s2 /\
  lift_result R (Halt s1) (Halt s2) = R s1 s2 /\
  lift_result R (Revert s1) (Revert s2) = R s1 s2 /\
  lift_result R (Error e1) (Error e2) = T /\
  lift_result R _ _ = F
End

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

(* ===== Simulation predicates (parameterized by R) ===== *)

(* Level 1: per-instruction simulation.
   f preserves lift_result R for every instruction and state,
   and preserves the is_terminator property. *)
Definition inst_simulates_def:
  inst_simulates R f <=>
    (!inst s. lift_result R (step_inst inst s) (step_inst (f inst) s)) /\
    (!inst. is_terminator inst.inst_opcode =
            is_terminator (f inst).inst_opcode)
End

(* Level 2: whole-block simulation.
   Running the transformed block gives an R-related result. *)
Definition block_simulates_def:
  block_simulates R bt <=>
    !bb s. lift_result R (run_block bb s) (run_block (bt bb) s)
End
