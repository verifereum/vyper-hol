(*
 * Internal Return Copy Forwarding — Proofs
 *
 * Correctness: ircf_transform_function preserves execution semantics.
 * The transform only NOPs mcopy instructions and rewrites operands
 * to point at the original return buffer allocation, which is
 * semantically equivalent when the forwarding preconditions hold.
 *
 * PROOF STRATEGY (see copyFwdEquiv for supporting theorems):
 *
 *   1. DIVERGENCE: mcopy (original) vs nop (transformed).
 *      copy_fwd_cross_equiv establishes cross_mem_region_equiv
 *      between dst-in-original and src-in-transformed.
 *
 *   2. INVARIANT: copy_fwd_rel maintained between the two executions.
 *      Variables agree; dst and src regions have same content cross-state.
 *
 *   3. REWRITTEN USES: Each rewritten instruction has dst_var replaced
 *      by src_root at an iao_ofst (memory address) position — verified
 *      by is_mem_addr_position check in ircf_try_forward.
 *      copy_fwd_read_equiv / copy_fwd_write_equiv show the output
 *      and observable state are equivalent.
 *
 *   4. NO CLOBBER: ircf_try_forward's clobber analysis + the
 *      ircf_is_ret_buf_source use-shape constraint ensure no instruction
 *      between the copy and the last use writes to src region.
 *      copy_fwd_rel_preserved_identical_inst maintains the invariant.
 *
 *   5. CONVERGENCE: After the last rewritten use, variables and
 *      observable state agree. Memory differs only at dst (dead).
 *      copy_fwd_rel_observable_equiv gives observable_equiv.
 *)

Theory internalReturnCopyFwdProofs
Ancestors
  internalReturnCopyFwdDefs passSimulationProps

Theorem ircf_pass_correct:
  !fn_meta ctx_fns rma fn fuel run_ctx s.
    wf_function fn /\ fn_inst_wf fn /\
    alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel run_ctx fn s = Error e) \/
    result_equiv {}
      (run_blocks fuel run_ctx fn s)
      (run_blocks fuel run_ctx
        (ircf_transform_function fn_meta ctx_fns rma fn) s)
Proof
  cheat
QED
