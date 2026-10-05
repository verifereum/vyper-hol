(* Proof-local normalization regenerated from the record datatype. Only
   residual-mask equality is expanded; arbitrary state equalities are left
   intact. No fixed-selector comparison is saved as a theory interface. *)
structure lowerDloadFrameLib = struct
open HolKernel boolLib bossLib;
open lowerDloadFrameTheory venomStateTheory;

val frame_ss = simpLib.rewrites (map
  (SIMP_CONV (srw_ss())
    [ld_frame_def, ld_execution_frame_def, venom_state_component_equality])
  [``ld_frame s1 = ld_frame s2``,
   ``ld_execution_frame s1 = ld_execution_frame s2``]);
end
