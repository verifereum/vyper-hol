(* Proof-local normalization from the CURRENT record datatype. Only mask
   equalities are expanded, never arbitrary state equality. No frozen-selector
   comparison is saved/exported as a production interface. *)
structure memzeroFrameLib = struct
open HolKernel boolLib bossLib;
open memzeroFrameTheory venomStateTheory;

val frame_ss = simpLib.rewrites [SIMP_CONV (srw_ss())
  [memzero_frame_def, venom_state_component_equality]
  ``memzero_frame s1 = memzero_frame s2``];
end
