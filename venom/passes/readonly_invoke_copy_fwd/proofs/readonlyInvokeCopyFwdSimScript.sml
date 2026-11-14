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
  readonlyInvokeCopyFwdExecutionFamily readonlyInvokeCopyFwdExecutionAssembly
  readonlyInvokeCopyFwdExecutionTransform
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
  rpt gen_tac >> strip_tac >> gvs[] >>
  mp_tac (Q.INST [`fn_meta` |-> `icf_fn_meta_of C`,
    `rma` |-> `readonly_mem_analyze C`]
    (SPEC_ALL ricf_execution_transform_midpoints)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qabbrev_tac `Ct = ricf_transform_ctx (icf_fn_meta_of C) (readonly_mem_analyze C) C` >>
  qabbrev_tac `R = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_boundary vs C mid_of log_of D a U B0 E0
      outer_history outer_certificates sites maps targets)` >>
  qabbrev_tac `Rret = (\(a,U,B0,E0,outer_history,outer_certificates,sites,maps,targets).
    ricf_execution_return vs C Ct mid_of log_of D a U B0 E0
      outer_history outer_certificates sites maps targets)` >>
  `!f. MEM f C.ctx_functions ==>
    ricf_logged_function_trace
      (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) f)
      f (log_of f) (mid_of f) /\ ricf_function_edit f (mid_of f) /\
    ?f'. lookup_function f.fn_name Ct.ctx_functions = SOME f' /\
      fn_entry_label f' = fn_entry_label f` by
    (rpt strip_tac >>
     qpat_x_assum `!fn. MEM fn _ ==> ricf_function_trace _ _ _ /\ _`
       (qspec_then `f` mp_tac) >> simp[] >> strip_tac >> simp[] >>
     qexists_tac `if (mid_of f).fn_blocks <> f.fn_blocks
       then clear_nops_function (mid_of f) else mid_of f` >>
     fs[Abbr `Ct`]) >>
  `!fn fn'. MEM fn C.ctx_functions /\
    lookup_function fn.fn_name Ct.ctx_functions = SOME fn' ==>
    fn' = if (mid_of fn).fn_blocks <> fn.fn_blocks
          then clear_nops_function (mid_of fn) else mid_of fn` by
    (rpt strip_tac >>
     qpat_x_assum `!fn. MEM fn _ ==> ricf_function_trace _ _ _ /\ _`
       (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
     gvs[Abbr `Ct`]) >>
  mp_tac (SPEC_ALL ricf_execution_family) >>
  (impl_tac >- simp[Abbr `R`,Abbr `Rret`]) >> strip_tac >>
  mp_tac (SPEC_ALL ricf_execution_context_from_family) >>
  (impl_tac
   >- (gvs[Abbr `Ct`,Abbr `R`,Abbr `Rret`] >>
       rpt strip_tac >> metis_tac[])) >> simp[]
QED
