(* Proof-local normalization derived from the CURRENT record datatype.
   Expand ONLY DSE mask equalities, never arbitrary state equality.
   No fixed-selector theorem is saved/exported. Future fields are included
   automatically by the datatype-generated component equality theorem. *)
structure deadStoreElimFrameLib = struct
open HolKernel boolLib bossLib;
open deadStoreElimFrameTheory venomStateTheory;

val frame_ss = simpLib.rewrites (map
  (SIMP_CONV (srw_ss())
    [dse_frame_def, dse_all_frame_def, venom_state_component_equality])
  [``dse_frame space s1 = dse_frame space s2``,
   ``dse_all_frame s1 = dse_all_frame s2``]);
end
