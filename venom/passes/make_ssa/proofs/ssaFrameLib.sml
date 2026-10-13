(* Proof-local normalization, generated from the CURRENT record datatype.
   Only residual-mask equalities are expanded, never arbitrary state equality.
   These rules are not saved/exported as fixed-selector theory interfaces. *)
structure ssaFrameLib = struct
open HolKernel boolLib bossLib;
open ssaFrameTheory venomStateTheory;

val frame_ss = simpLib.rewrites (map
  (SIMP_CONV (srw_ss())
    [ssa_frame_def, ssa_execution_frame_def, venom_state_component_equality])
  [``ssa_frame s1 = ssa_frame s2``,
   ``ssa_execution_frame s1 = ssa_execution_frame s2``]);
end
