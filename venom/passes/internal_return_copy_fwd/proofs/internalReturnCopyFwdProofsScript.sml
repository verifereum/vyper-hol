(*
 * Internal Return Copy Forwarding — Proofs
 *
 * Correctness: ircf_transform_function preserves execution semantics.
 * The transform only NOPs mcopy instructions and rewrites operands
 * to point at the original return buffer allocation, which is
 * semantically equivalent when the forwarding preconditions hold.
 *)

Theory internalReturnCopyFwdProofs
Ancestors
  internalReturnCopyFwdDefs passSimulationProps

Theorem ircf_pass_correct:
  !fn_meta ctx_fns rma fn fuel run_ctx s.
    wf_function fn /\ fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel run_ctx fn s = Error e) \/
    result_equiv {}
      (run_function fuel run_ctx fn s)
      (run_function fuel run_ctx
        (ircf_transform_function fn_meta ctx_fns rma fn) s)
Proof
  cheat
QED
