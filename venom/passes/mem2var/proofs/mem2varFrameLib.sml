(* Proof-local normalization from the CURRENT record datatype. Only mask
   equalities are expanded, never arbitrary state equality. No frozen-selector
   comparison is saved/exported as a production interface. *)
structure mem2varFrameLib = struct
open HolKernel boolLib bossLib;
open mem2varFrameTheory venomStateTheory;

val frame_ss = simpLib.rewrites [SIMP_CONV (srw_ss())
  [m2v_frame_def, venom_state_component_equality]
  ``m2v_frame s1 = m2v_frame s2``];
end
