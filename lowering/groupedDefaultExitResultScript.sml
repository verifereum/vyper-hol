(* The exceptional default-expression endpoint, before binding arguments. *)
Theory groupedDefaultExitResult
Ancestors
  groupedEntryExit groupedDefaultBinding groupedDefaultOutcome sourceUnitExecution
  loweringHalt exprSimDefs fragGasOriginPtr gasSummary gasExplicitSites
  e2eDefs vyperInterpreter vyperState vyperContext vyperStorageFootprint
  venomInst venomState fragExec ptrDiscipline

Theorem grouped_default_exit_rel[local]:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  expr_exit (INR ex : value list + exception) r /\
  halt_exit H cx (ee with gas_obs := []) (INR ex : value list + exception) r ==>
  external_call_result_rel H tops ret tx
    (INR ex, if ex = HaltException then finalize_pending_deletions
       (abstract_machine_from_state am.sources am.exports am.layouts ee)
     else am, ee.requests) r
Proof
  rpt strip_tac >>
  Cases_on `r` >> Cases_on `ex` >>
  gvs[halt_exit_def, expr_exit_def, external_call_result_rel_def] >>
  TRY (rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >>
    gvs[expr_exit_def, external_call_result_rel_def] >> NO_TAC) >>
  drule external_halt_rel_success >>
  simp[initial_evaluation_context_def, abstract_machine_from_state_def] >>
  metis_tac[]
QED

Theorem grouped_default_exception_result:
  source_deployment_rel tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := SOME vs.vs_outcomes; requests := []|>) =
    (INL (),es) /\ es.scopes = [FEMPTY] /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0 /\
  gas_shadow_context unit.cu_context shadow_ctx /\
  gas_shadow_function fn shadow_fn /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  storage_trace_domain cx (initial_state am []) es.storage_trace /\
  ee.storage_trace = es.storage_trace /\
  (!tail. eval_exprs cx
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
    (es with gas_obs := gas_explicit marks vs.vs_gas_readings ++ tail) =
    (INR ex,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx (initial_state am []) H es.storage_trace ==>
    gas_origin_ptr_path
      (cx_dead H cx,0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context,fn,[])
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
       FEMPTY,entry_taint) [] (OK s,G,tn)) /\
  ((?r J tz. exit_result r /\
      create_size_exit_ok unit.cu_context (INR ex : value list + exception) r /\
      !H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
        gas_origin_ptr_path
          (cx_dead H cx,0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context,fn,[])
          (s,G,tn) marks (r,J,tz) /\
        expr_exit (INR ex : value list + exception) r /\
        halt_exit H cx (ee with gas_obs := []) (INR ex : value list + exception) r) \/
   (?err H leaf leaf_pg leaf_g leaf_tn finish.
      ex = Error err /\ unspecified_behaviour_exempt tops err /\
      valid_horizon cx (initial_state am []) H es.storage_trace /\
      gas_origin_ptr_focus
        (cx_dead H cx,0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context,fn,[])
        (s,G,tn) marks (leaf,leaf_pg,leaf_g,leaf_tn,finish))) ==>
  source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs /\
  ((?tail. call_storage_ok am tx vs.vs_outcomes
     (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
   !tail. FST (call_external (SOME vs.vs_outcomes)
     (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
       INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v. ex <> ReturnException v` by
    (qpat_assum `(?r J tz. _) \/ _` strip_assume_tac
     >- (`valid_horizon cx (initial_state am [])
           (storage_trace_horizon es.storage_trace) ee.storage_trace` by
           metis_tac[storage_trace_domain_def] >>
         qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
           (drule_then strip_assume_tac) >>
         rpt strip_tac >> Cases_on `r` >> gvs[expr_exit_def]) >>
     simp[]) >>
  drule_all grouped_default_initializer_exception_trace >> strip_tac >>
  drule grouped_default_readings_not_missing >>
  disch_then (assume_tac o REWRITE_RULE [sumTheory.INR_11]) >>
  reverse conj_tac
  >- (strip_tac >> qx_gen_tac `unread` >>
      qpat_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `unread` (strip_assume_tac o MATCH_MP call_external_trace_result)) >>
      asm_rewrite_tac[pairTheory.FST, sumTheory.INR_11]) >>
  qpat_x_assum `(?r J tz. _) \/ _` strip_assume_tac
  >- suspend "matched" >>
  suspend "exempt"
QED

Resume grouped_default_exception_result[matched]:
  `create_size_exit_ok unit.cu_context (INR ex : value + exception) r` by
    fs[createSizeExitTheory.create_size_exit_ok_inr] >>
  qsuff_tac `source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs /\
    !tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))` >- simp[] >>
  irule grouped_entry_matched_exit >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`if ex = HaltException then finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts ee) else am`,
    `bb`,`cx`,`fn`,`ee.storage_trace`,`r`,`INR ex`,`ee.requests`,
    `vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>`,
    `shadow_fn`] >>
  asm_rewrite_tac[sumTheory.INR_11] >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx (initial_state am []) H ee.storage_trace` by metis_tac[] >>
  `valid_horizon cx (initial_state am []) H es.storage_trace` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- (irule grouped_default_exit_rel >> metis_tac[]) >>
  qexistsl_tac [`J`,`tz`] >>
  qpat_assum `cx = _` (fn th => pure_rewrite_tac [SYM th]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> gas_origin_ptr_path _ _ [] _`
    (drule_then assume_tac) >>
  metis_tac[gas_origin_ptr_path_append, listTheory.APPEND]
QED

Resume grouped_default_exception_result[exempt]:
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  PURE_REWRITE_TAC [source_unit_execution_correct_with_def] >>
  qexistsl_tac [`fn`,`shadow_fn`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[lookup_function_MEM] >>
  disj2_tac >>
  qexistsl_tac [`INR (Error err)`,`am`,`ee.requests`,`ee.storage_trace`] >>
  fs[] >> disj1_tac >> simp[source_exempt_def] >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_focus _ _ _ (_,_,_,_,u_end)` >>
  qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`u_end`] >>
  irule (SIMP_RULE (srw_ss()) [listTheory.APPEND]
    (Q.INST [`left` |-> `[]`] (SPEC_ALL (cj 2 gas_origin_ptr_focus_rules)))) >>
  metis_tac[]
QED

Finalise grouped_default_exception_result
