(* Locate a reached pre-instruction on the very same native execution. *)
Theory entryCreateNativeCut
Ancestors
  dftGasFromListLocator dftGasFromListTracePrefix dftGasFromListReadings
  dftGasFromListTraceDefs venomExecSemantics list arithmetic

Theorem selected_context_trace_stable[local]:
  bound <= larger /\ (!err. run_context bound C vi <> Error err) ==>
  trace_context larger C vi = trace_context bound C vi
Proof
  Cases_on `C.ctx_entry` >> simp[trace_context_def, run_context_def] >>
  rename1 `C.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm C.ctx_functions` >> simp[] >>
  rename1 `lookup_function nm C.ctx_functions = SOME root` >>
  Cases_on `fn_entry_label root` >>
  simp[trace_function_def, run_function_def] >>
  strip_tac >> irule (cj 3 trace_stable) >> simp[]
QED

(* p records the suspended invocations, d the block occurrence in this
   invocation. The visit itself is not executed in the prefix. In
   particular the theorem does not ask for an outcome or a recording edge
   at the visit. *)
Theorem reached_on_selected_prefix:
  EVERY wf_function C.ctx_functions /\
  (!err. run_context bound C vi <> Error err) /\
  raw_reachable vi C fn inst s ==>
  ?p d pre post.
    trace_context bound C vi = pre ++ ((p,d,inst.inst_id),fn,inst,s)::post /\
    trace_gas (trace_context bound C vi) =
      trace_gas pre ++ visit_gas ((p,d,inst.inst_id),fn,inst,s) ++ trace_gas post
Proof
  strip_tac >> drule_all raw_reachable_trace >> strip_tac >>
  `trace_context (MAX bound fuel) C vi = trace_context bound C vi` by
    (irule selected_context_trace_stable >> simp[]) >>
  `fuel <= MAX bound fuel` by simp[] >>
  drule trace_context_prefix >>
  disch_then (qspecl_then [`vi`, `C`] strip_assume_tac) >>
  `MEM ((p,d,inst.inst_id),fn,inst,s) (trace_context bound C vi)` by
    metis_tac[MEM_APPEND] >>
  qpat_x_assum `MEM _ (trace_context bound C vi)`
    (strip_assume_tac o ONCE_REWRITE_RULE [MEM_SPLIT]) >>
  qexistsl [`p`, `d`, `l1`, `l2`] >> simp[]
QED
