(*
 * transfer_sound_exit_from_wf: generalized exit soundness
 * starting from arbitrary vs_inst_idx (not just 0).
 *
 * Theorems are now defined in analysisSimProofsScript.sml (Part 1).
 * This file re-exports them for backward compatibility.
 *)

Theory analysisSimProofsFromWf
Ancestors
  analysisSimProofs list finite_map pred_set string

(* All theorems are inherited from analysisSimProofsTheory:
   transfer_sound_exit_from_wf_ind
   transfer_sound_exit_from_wf
   transfer_sound_exit_from_wf_len
 *)
