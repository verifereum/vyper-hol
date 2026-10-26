(* Compiler entry fields used by call correctness. *)
Theory e2eCallChecks
Ancestors
  e2eEntry

(* Consume the existing entry helper GROUPS, not a strengthened top premise.
 * Exact FMP/calldata are initialized here; labels and outcomes are concrete.
 * No memory invariant is claimed: its witness is supplied later by S5.
 *)
Theorem call_entry_compiler_fields:
  !prog cp es.
  (entry_venom_state prog cp es).vs_outcomes = MAP SND (call_trace es) /\
  (entry_venom_state prog cp es).vs_requests = [] /\
  (entry_venom_state prog cp es).vs_call_ctx.cc_calldata =
    (FST (HD es.contexts)).msgParams.data /\
  (entry_venom_state prog cp es).vs_initial_fmp = n2w cp.cp_initial_fmp /\
  initial_codegen_state_rel cp (entry_venom_state prog cp es) /\
  (!l. FLOOKUP (entry_venom_state prog cp es).vs_labels l =
       OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l))
Proof
  simp[entry_venom_state_frame_fields, entry_venom_state_fresh,
       entry_venom_state_def]
QED
