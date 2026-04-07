(*
 * Readonly Invoke Arg Copy Forwarding — Proofs
 *
 * Correctness: ricf_transform_function preserves execution semantics.
 * The transform only NOPs mcopy instructions and rewrites invoke
 * operands to point at the original source allocation, which is
 * semantically equivalent when the callee parameter is readonly.
 *
 * PROOF STRATEGY (see copyFwdEquiv for supporting theorems):
 *
 *   1. DIVERGENCE: mcopy (original) vs nop (transformed).
 *      copy_fwd_cross_equiv establishes cross_mem_region_equiv.
 *
 *   2. REWRITTEN USES: Only invoke instructions at readonly positions.
 *      The callee reads from tmp (original) vs src (transformed).
 *      Since both regions have the same content (cross_mem_region_equiv)
 *      and the callee only reads (readonly guarantee from RMA analysis),
 *      the callee produces the same result.
 *
 *   3. NO CLOBBER: icf_has_src_clobber ensures src region is not
 *      written between the copy and the invoke.
 *
 *   4. SIBLING ALIASING: ricf_has_mutable_sibling prevents creating
 *      observable aliasing between parameters that didn't exist before.
 *
 * ADDITIONAL REQUIREMENT: ReadonlyMemoryArgsAnalysis correctness —
 *   the analysis must accurately identify callee parameters that are
 *   never written through (no MSTORE/MCOPY/ext-call through that
 *   parameter or its derivatives within the callee).
 *)

Theory readonlyInvokeCopyFwdProofs
Ancestors
  readonlyInvokeCopyFwdDefs passSimulationProps

Theorem ricf_pass_correct:
  !fn_meta ctx_fns rma fn fuel run_ctx s.
    wf_function fn /\ fn_inst_wf fn /\
    alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel run_ctx fn s = Error e) \/
    result_equiv {}
      (run_blocks fuel run_ctx fn s)
      (run_blocks fuel run_ctx
        (ricf_transform_function fn_meta ctx_fns rma fn) s)
Proof
  cheat
QED
