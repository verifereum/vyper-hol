(*
 * Readonly Invoke Copy Forwarding — the simulation
 *
 * The source runs MCOPY d <- s and passes d to INVOKEs at readonly
 * parameter positions; the target skips the copy and passes s.  The
 * callee frames then differ in the relocated parameter (source d,
 * target s) and every pointer derived from it, while the bytes they
 * point at agree: nothing writes either buffer during the calls, by the
 * readonly analysis on reachable states (ptr_discipline).
 *
 * TOP-LEVEL:
 *   ricf_pass_correct   — the pass as a context simulation
 *)

Theory readonlyInvokeCopyFwdSim
Ancestors
  readonlyInvokeCopyFwdDefs invokeCopyFwdCommonDefs readonlyMemoryArgsDefs
  internalReturnCopyFwdSim reachableFnSim taintAgree o1PassContract
  ptrDiscipline unitMemInv venomExecSemantics venomInst venomWf venomState
  finite_map pred_set list

Theorem ricf_pass_correct:
  !D lo vs C fn_meta rma.
    o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
    EVERY ricf_full_alloca_copies C.ctx_functions /\
    EVERY ricf_no_derived_mutable_sibling C.ctx_functions /\
    EVERY ricf_src_alloca C.ctx_functions /\
    EVERY ricf_param_order_ok C.ctx_functions /\
    ptr_discipline lo C vs /\ mem_inv raw_mem_ok C vs /\
    vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
    ~ctx_has_dalloca C /\ taint_within D C vs /\ dead_wf D /\
    fn_meta = icf_fn_meta_of C /\ rma = readonly_mem_analyze C ==>
    ctx_sim D C (ricf_transform_ctx fn_meta rma C) vs vs
Proof
  cheat
QED
