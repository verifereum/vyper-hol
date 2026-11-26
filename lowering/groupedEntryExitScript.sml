(* Matched exits before the grouped entry binds its arguments. *)
Theory groupedEntryExit
Ancestors
  createSizeExit sourceUnitExecution e2eDefs gasSummary gasExplicitSites fragGasOriginPtr
  fragGasOriginPtrExec fragExec fragExecPtr entryDispatchPtr ptrSafeRun
  ptrDiscipline vyperStorageFootprint venomInst venomState venomExecSemantics
  vyperCall vyperState vyperEvalReadingErrors list
  externalEntryValueRevert externalEntryChecks fragGasOrigin vyperInterpreter

val _ = Parse.hide "body";

Theorem grouped_entry_matched_exit:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 /\
  gas_shadow_context unit.cu_context shadow_ctx /\
  gas_shadow_function fn shadow_fn /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  (!tail. call_external_trace (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs)) /\
  res <> INR (Error (RuntimeError "msg.gas: no gas reading")) /\
  storage_trace_domain cx (initial_state am []) obs /\ exit_result r /\
  create_size_exit_ok unit.cu_context res r /\
  (!H. valid_horizon cx (initial_state am []) H obs ==>
    external_call_result_rel H tops ret tx (res,am',rqs) r /\
    ?G tn. gas_origin_ptr_path
      (cx_dead H cx,0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context,fn,[])
      (s,FEMPTY,entry_taint) marks (r,G,tn)) ==>
  source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs /\
  !tail. FST (call_external (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
      INR (Error (RuntimeError "msg.gas: no gas reading"))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (qpat_x_assum `cx = _` SUBST_ALL_TAC >>
      PURE_REWRITE_TAC [source_unit_execution_correct_with_def] >>
      qexistsl_tac [`fn`,`shadow_fn`] >> asm_rewrite_tac[] >>
      conj_tac >- metis_tac[lookup_function_MEM] >>
      disj2_tac >> qexistsl_tac [`res`,`am'`,`rqs`,`obs`] >> asm_rewrite_tac[] >>
      disj2_tac >> qexists_tac `r` >>
      qpat_assum `s = _` (fn th => PURE_REWRITE_TAC [SYM th]) >>
      asm_rewrite_tac[] >> conj_tac
      >- (qpat_assum `storage_trace_domain _ _ _` (strip_assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
          metis_tac[gas_origin_ptr_path_projections]) >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      asm_rewrite_tac[] >>
      irule ptr_safe_blocks_from_phi_free_run >>
      reverse conj_tac >- (simp[] >> metis_tac[]) >>
      qpat_assum `s = _` (fn th => PURE_REWRITE_TAC [SYM th]) >>
      drule gas_origin_ptr_path_exec >> strip_tac >>
      gvs[exit_result_def] >>
      irule fragExecPtrTheory.ptr_safe_run_all_fuel >>
      metis_tac[exit_result_not_error]) >>
  gen_tac >>
  qpat_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `tail` (strip_assume_tac o MATCH_MP call_external_trace_result)) >>
  simp[]
QED

Theorem grouped_entry_value_rejected:
  source_deployment_rel tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,defaults,ret,body) /\
  LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH defaults /\
  mut <> Payable /\ tx.value <> 0 /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0 /\
  gas_shadow_context unit.cu_context shadow_ctx /\
  gas_shadow_function fn shadow_fn /\ MEM shadow_fn shadow_ctx.ctx_functions /\
  compile_entry_checks m F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
  ~block_is_terminated opened /\ fresh_vars_wrt opened t /\
  ~t.vs_halted /\ t.vs_current_bb = opened.cs_current_bb /\
  t.vs_inst_idx = 0 /\ allocas_from 0 t /\
  (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp t) /\
  t.vs_call_ctx.cc_callvalue <> 0w /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,fn,[])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>,
     FEMPTY,entry_taint) [] (OK t,G,tn)) ==>
  source_unit_execution_correct_with shadow_ctx [] tops ret am tx unit vs /\
  !tail. FST (call_external (SOME vs.vs_outcomes) tail am tx) <>
    INR (Error (RuntimeError "msg.gas: no gas reading"))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_value_reject_trace >>
  disch_then (qspec_then `SOME vs.vs_outcomes` assume_tac) >>
  drule_all nonpayable_check_joint_reject >>
  disch_then (qspecl_then [`tn`, `[]`, `G`] mp_tac) >>
  disch_then (qx_choosel_then [`u`,`J`,`tz`] strip_assume_tac) >>
  irule (SIMP_RULE (srw_ss()) [gas_explicit_def] (Q.INST [`marks` |-> `[]`]
    grouped_entry_matched_exit)) >>
  simp[] >>
  qexistsl_tac [`Abort Revert_abort u`, `shadow_fn`] >>
  simp[exit_result_def, external_call_result_rel_def,
       createSizeExitTheory.create_size_exit_ok_non_exhalt] >>
  reverse conj_tac
  >- simp[storage_trace_domain_def, valid_horizon_def, storage_trace_horizon_def,
       storage_trace_regions_def, storage_trace_locks_def, storage_observations_ok_def,
       regions_consistent_def, storage_locks_separated_def, storage_well_formed_on_def,
       storage_roots_fit_def, storage_trace_backends_well_formed_def] >>
  rpt strip_tac >> qexistsl_tac [`J`,`tz`] >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED
