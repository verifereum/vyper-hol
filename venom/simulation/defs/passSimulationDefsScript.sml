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
 *   lift_result              — dual-relation lift through exec_result
 *   block_map_transform      — MAP f over block instructions
 *   function_map_transform   — MAP bt over function blocks
 *   inst_simulates           — per-instruction simulation predicate
 *   block_simulates          — whole-block simulation predicate
 *)

Theory passSimulationDefs
Ancestors
  venomExecSemantics venomInst

(* ===== Result relation ===== *)

(* Lift two state relations through exec_result.
   R_ok for OK (continuation), R_term for Halt/Revert (terminal). *)
Definition lift_result_def:
  lift_result R_ok R_term (OK s1) (OK s2) = R_ok s1 s2 /\
  lift_result R_ok R_term (Halt s1) (Halt s2) = R_term s1 s2 /\
  lift_result R_ok R_term (Revert s1) (Revert s2) = R_term s1 s2 /\
  lift_result R_ok R_term (Error e1) (Error e2) = T /\
  lift_result R_ok R_term _ _ = F
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
