(* A failed runtime lock has no request-site observation. *)
Theory s1PrefixLockAbort
Ancestors
  s1PrefixDefs fragGasOriginPtr gasExplicitSites gasSummary
  nonreentrantEquiv vfmState vyperCall vyperContext vyperInterpreter vyperState
  venomInst venomState finite_map list words
  bodyFullIntCallCallee[qualified,ignore_grammar]

Theorem selected_lock_abort_prefix_cert:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  entry = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  gas_origin_ptr_focus
    (cx_dead (H0 : (bool # bytes32 # type_value) list # num list) cx,0,
     gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context,func,[])
    (entry,FEMPTY,entry_taint) marks (func,[],G0,tn0,s0) /\
  es0.storage_trace = [] /\
  lock_if_nr cx nr view es0 = (INR exc,es_abort) /\
  (!tail. call_external_trace (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
    (INR exc,am,es_abort.requests,es_abort.storage_trace)) ==>
  unit_prefix_cert shadow_ctx tops am tx unit vs
Proof
  strip_tac >>
  `!rq outcome. ~MEM (StorageOutcome rq outcome) es_abort.storage_trace` by
    (drule bodyFullIntCallCalleeTheory.intcall_callee_lock_no_outcome >> simp[]) >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  qpat_x_assum `entry = _` SUBST_ALL_TAC >>
  pure_rewrite_tac[unit_prefix_cert_def] >> qexistsl_tac [`func`,`marks`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexistsl_tac [`H0`,`func`,`[]`,`G0`,`tn0`,`s0`] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `tail` assume_tac) >>
  `obs = es_abort.storage_trace` by metis_tac[pairTheory.PAIR_EQ] >>
  `MEM (StorageOutcome rq outcome) obs` by
    (qpat_assum `obs = obs_pre ++ _` (fn split => pure_rewrite_tac[split]) >>
     simp[MEM_APPEND]) >>
  metis_tac[]
QED
