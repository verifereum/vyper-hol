(*
 * S1 on finite storage horizons: the lowered runtime unit runs the
 * external function valid_vyper_call selects as the source does
 * (sourceUnitExecution's source_unit_execution_correct).
 *
 * lower_vyper_runtime_unit_body_joint, when the call value moves and the
 * body starts, composes:
 *   - the entry (externalEntryJoint): from the unit's initial state the
 *     run reaches the selected body's start along a zero-mark memory path,
 *     at the compile state runtime_selected_body_start pins;
 *   - the body's frame (externalBodyFrame) and returns
 *     (externalFrameRetOk) at every valid horizon;
 *   - the shadow placement (runtimeBodyShadow): the unit's GAS shadow
 *     from gas_shadow_run_lowering holds the shadow body's code;
 *   - the body (bodySimFullMain's body_stmts_sim_full);
 *   - the fall-through STOP of a body without a return type;
 *   - the source call's storage observations, which are the body's
 *     (externalCallSelected), so a run outside every horizon violates the
 *     unit's storage guards.
 *
 * lower_vyper_runtime_unit_correct splits on whether the call value
 * moves: the body joint above, or externalEntryValueRevert's abort.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_correct -- S1
 *   lower_vyper_runtime_unit_body_joint -- S1 when the value moves
 *   runtime_body_joint_from_start -- the same, from the entry's endpoint
 *   lower_vyper_runtime_unit_run_bounded -- S1b (sufficient gas)
 *)

Theory loweringRuntimeCorrect
Ancestors
  bodyFullShadowBodyInvLowering
  sourceUnitExecution e2eDefs compileVyper vyperInterpreter vyperState
  vyperStorageFootprint gasShadowUnit vyperTypeSelectedEntrySoundness
  externalEntryValueRevert unitExecutionCompose externalEntryJoint entryDispatchProps
  gasShadowRunLowering gasShadowUnitGuards fragGasOriginPtrExec
  runtimeEntryEndpoint runtimeBodyStartDefs externalEntryBound
  runtimeFallbackSourceAlignment runtimeFallbackPackageEnvironment
  externalBodyFrame externalFrameRetOk runtimeBodyShadow externalBodySupport
  externalReturnPackage compileEnv
  exprSimHypsDefs vyperTypeInvariants
  stmtSimProps stmtsEnvRetTy gasSummary
  constSubst constSubstStmtsPreserve
  externalCallSelected externalBodySourceOk bodySimFullMain bodySimFull bodyFullPreds bodyLoopCalls
  entryStateRel entryReachBodyFmp entryReachBodyRuntimeResources
  bodyAbiDecodeTarget rawReturnHeader loweringHalt gasContext bodyPtrDefs
  gasOutcomeFull fragGasOriginPtr loweringPosts stmtSimDefs exprSimDefs
  exprLoweringProps vyperStorageTrace vyperStorageBackend vyperCall
  fragExec moduleLowering fragGasOrigin fragFuelUnit passSimulationDefs
  acceptedContextPhi vyperLoweringCorrect typedCopyProducer
  deployBodyReachability contextRawReachable contextCodegenRel unitTransformDefs
  venomInst venomState ptrDiscipline list
  vyperEvalReadingErrors unitExecutionComposeResult vyperCalldata supportedProgram
  groupedEntryExit groupedSelectedDefault groupedRegisteredBody groupedRuntimeEndpoint
  groupedRuntimeBodyCode groupedEntryCut groupedDefaultCode groupedDefaultBinding
  groupedDefaultSubstitution groupedDefaultArguments groupedDefaultState
  groupedDefaultSource groupedDefaultSyntax groupedKeywordInitialize groupedEntryCommon
  groupedEntryAllocation groupedDefaultOutcome groupedDefaultPre
  registrationRejectMetadata rejectPrefixSourceShape entryRejectAllocationIds
  defaultDispatchFacts groupedCanonicalCallRoute groupedDefaultCallRoute
  groupedFallbackCallRoute groupedLegacyCallRoute

val _ = Parse.hide "body";

(* ===== The source's result ===== *)

(* call_external_body without a lock, from es0 in the bound scope, where
   the body ran to es'. *)
Theorem call_external_body_run:
  !am cx mut tenv env fbody ret es0 res es'.
    es0.scopes = [env] /\
    eval_stmts cx fbody es0 = (res, es') ==>
    (res = INL () ==>
     call_external_body am cx F mut tenv es0 env fbody ret =
       (INL NoneV,
        abstract_machine_from_state am.sources am.exports am.layouts es',
        es'.requests)) /\
    (!v. res = INR (ReturnException v) ==>
     call_external_body am cx F mut tenv es0 env fbody ret =
       case evaluate_type tenv ret of
         NONE => (INR (Error (TypeError "eval ret")), am, es'.requests)
       | SOME tv =>
           case safe_cast tv v of
             NONE => (INR (Error (TypeError "ext cast ret")), am,
                      es'.requests)
           | SOME v' =>
               (INL v',
                abstract_machine_from_state am.sources am.exports am.layouts
                  es', es'.requests)) /\
    (res = INR HaltException ==>
     call_external_body am cx F mut tenv es0 env fbody ret =
       (INR HaltException,
        abstract_machine_from_state am.sources am.exports am.layouts es',
        es'.requests)) /\
    (!e. res = INR e /\ (!v. e <> ReturnException v) /\ e <> HaltException ==>
     call_external_body am cx F mut tenv es0 env fbody ret =
       (INR e, am, es'.requests))
Proof
  rpt gen_tac >> strip_tac >>
  `es0 with scopes := [env] = es0` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[call_external_body_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.set_scopes_def] >>
  rpt strip_tac >> gvs[]
  >- (BasicProvers.EVERY_CASE_TAC >> gvs[])
  >> Cases_on `e` >> gvs[]
QED

(* ===== The source call in terms of its body ===== *)

(* The selected call at gas observations gx, from the body's run at gx:
   its observations are the body's, and its result is the body's. *)
Theorem selected_call_trace_body[local]:
  !tops am tx ret mut args fbody env os gx es0 res ee.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME os; requests := [] |>) = (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es0 with gas_obs := gx) = (res, ee) ==>
    ?r am' rqs.
      call_external_trace (SOME os) gx am tx =
        (r, am', rqs, ee.storage_trace) /\
      (res = INL () ==>
         r = INL NoneV /\ rqs = ee.requests /\
         am' = finalize_pending_deletions
                 (abstract_machine_from_state am.sources am.exports
                    am.layouts ee)) /\
      (res = INR HaltException ==>
         r = INR HaltException /\ rqs = ee.requests /\
         am' = finalize_pending_deletions
                 (abstract_machine_from_state am.sources am.exports
                    am.layouts ee)) /\
      (!v. res = INR (ReturnException v) ==>
         rqs = ee.requests /\
         (r, am') =
           case evaluate_type (type_env tops) ret of
             NONE => (INR (Error (TypeError "eval ret")), am)
           | SOME tv =>
               case safe_cast tv v of
                 NONE => (INR (Error (TypeError "ext cast ret")), am)
               | SOME v' =>
                   (INL v', finalize_pending_deletions
                              (abstract_machine_from_state am.sources
                                 am.exports am.layouts ee))) /\
      (!e. res = INR e /\ (!v. e <> ReturnException v) /\
           e <> HaltException ==>
         r = INR e /\ am' = am /\ rqs = ee.requests)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH tx.args = LENGTH args` by
    (drule bind_arguments_length >> simp[]) >>
  `lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
     F (is_view_mut mut) (es0 with gas_obs := gx) =
     (INL (), es0 with gas_obs := gx)` by
    simp[lock_if_nr_def, vyperStateTheory.return_def] >>
  drule_all call_external_selected_body_trace >>
  simp[unlock_if_nr_def, vyperStateTheory.return_def] >> strip_tac >>
  qexistsl_tac [`r`, `am'`, `rqs`] >> simp[] >>
  drule call_external_trace_result >> strip_tac >>
  drule_all call_external_selected_body_gas >>
  disch_then (qspec_then `gx` assume_tac) >>
  `es0.scopes = [env]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  `(es0 with gas_obs := gx).scopes = [env]` by simp[] >>
  `res = INR HaltException ==>
     call_external_body am
       (initial_evaluation_context am.sources am.layouts tx NONE)
       F mut (type_env tops) (es0 with gas_obs := gx) env fbody ret =
       (INR HaltException,
        abstract_machine_from_state am.sources am.exports am.layouts ee,
        ee.requests)` by
    (strip_tac >>
     `(es0 with gas_obs := gx) with scopes := [env] =
      es0 with gas_obs := gx` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     simp[call_external_body_def, vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
          vyperStateTheory.set_scopes_def]) >>
  drule_all call_external_body_run >>
  disch_then (qspecl_then [`am`, `mut`, `type_env tops`, `ret`]
                strip_assume_tac) >>
  rpt conj_tac
  >- (strip_tac >> gvs[])
  >- (strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v. res = INR (ReturnException v) ==> _`
        (qspec_then `v` mp_tac) >>
      gvs[] >> strip_tac >> gvs[] >> BasicProvers.every_case_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!e. res = INR e /\ _ ==> _` (qspec_then `e` mp_tac) >>
  simp[] >> strip_tac >> Cases_on `e` >> gvs[]
QED

(* The selected call is the same at two gas observations at which the body
   runs alike. *)
(* FAMILY TARGET: original failed proof retained for Alan; must be proved before delivery.
Proof
  rpt strip_tac >>
  qspecl_then [`tops`, `am`, `tx`, `ret`, `mut`, `args`, `fbody`, `env`,
               `os`, `g1`, `es0`, `res`, `ee with gas_obs := o1`] mp_tac
    selected_call_trace_body >>
  qspecl_then [`tops`, `am`, `tx`, `ret`, `mut`, `args`, `fbody`, `env`,
               `os`, `g2`, `es0`, `res`, `ee with gas_obs := o2`] mp_tac
    selected_call_trace_body >>
  simp[] >> rpt strip_tac >> simp[] >>
  qpat_x_assum `stmt_res_ok _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_res_ok_def]) >>
  gvs[abstract_machine_from_state_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[]
QED
*)
Theorem call_external_trace_observations[local]:
  !os gobs am tx.
    SND (SND (SND (call_external_trace (SOME os) gobs am tx))) =
    source_storage_trace am tx os gobs
Proof
  rpt gen_tac >>
  `?r am' rqs obs.
     call_external_trace (SOME os) gobs am tx = (r, am', rqs, obs)` by
    metis_tac[pairTheory.pair_CASES] >>
  drule call_external_trace_result >> simp[]
QED

(* ===== The body's end ===== *)

(* Falling off the end of a body without a return type: the guarded body's
   STOP halts with the body's effects, along a GAS-free pointer path of
   one exit edge. *)
Theorem compile_guarded_body_stop_path:
  !E ctx cenv nkey ut iv stmts st st' sb func t.
    compile_guarded_body cenv F nkey ut iv stmts NONE st = ((), st') /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb /\ fn_has_code sb st' func /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?ss.
      ss.vs_returndata = [] /\ ss.vs_accounts = t.vs_accounts /\
      ss.vs_transient = t.vs_transient /\ ss.vs_logs = t.vs_logs /\
      ss.vs_requests = t.vs_requests /\
      ss.vs_pending_deletions = t.vs_pending_deletions /\
      !H cx G tn.
        stor_taint_ok H cx tn t ==>
        ?G' tn'.
          gas_origin_ptr_path (cx_dead H cx, 0, E, ctx, func, [])
            (t, G, tn) [] (Halt ss, G', tn')
Proof
  rpt gen_tac >> strip_tac >>
  `st'.cs_current_bb = sb.cs_current_bb /\
   st'.cs_current_insts =
     sb.cs_current_insts ++ [mk_inst sb.cs_next_id STOP [] []]` by
    (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_guarded_body_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_return_def, compileEnvTheory.comp_get_def,
          emitHelperTheory.emit_inst_def, compileEnvTheory.fresh_id_def,
          compileEnvTheory.emit_def] >>
     rpt strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst sb.cs_next_id STOP [] []) t =
          Halt (halt_state (t with vs_returndata := []))` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke,
         venomInstTheory.mk_inst_def,
         venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
  `!fuel. gas_count_step fuel ctx (mk_inst sb.cs_next_id STOP [] []) t = 0` by
    simp[gasCountTheory.gas_count_step_def, venomInstTheory.mk_inst_def] >>
  `!fuel. gas_events_step fuel ctx func.fn_name
            (mk_inst sb.cs_next_id STOP [] []) t = []` by
    metis_tac[cj 1 gasEventsTheory.gas_events_length, listTheory.LENGTH_NIL] >>
  `!fuel. mem_safe_step fuel ctx (mk_inst sb.cs_next_id STOP [] []) t` by
    simp[memSafeRunTheory.mem_safe_step_non_invoke,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def,
         venomInstTheory.mk_inst_def] >>
  qexists_tac `halt_state (t with vs_returndata := [])` >>
  rpt conj_tac >~ [`gas_origin_ptr_path`]
  >- (rpt strip_tac >> qexistsl_tac [`G`, `tn`] >>
      `!fuel. ptr_safe_step (cx_dead H cx) 0 fuel ctx func [] G tn
                (mk_inst sb.cs_next_id STOP [] []) t` by
        (gen_tac >> simp[ptrSafeRunTheory.ptr_safe_step_def] >>
         irule fragExecPtrTheory.ptr_inst_ok_stop >> simp[]) >>
      irule (cj 3 gas_origin_ptr_path_rules) >>
      simp[exit_result_def, gas_origin_ptr_edge_def, gas_origin_edge_def,
           fragGasPathPtrTheory.gas_path_ptr_edge_def]) >>
  simp[venomStateTheory.halt_state_def]
QED

(* ===== S1 ===== *)

(* S1 when the value moves and the body starts, from the entry's endpoint
   (runtimeEntryEndpoint): unit_execution_compose of the entry's pointer
   path to the body's start and the body's gas_outcome_full, the call
   being call_external_trace at the call's outcomes.  Every entry that
   reaches the endpoint (the canonical one, any dispatched encoding, the
   __default__ fallback) shares this proof. *)
(* Shared bridge from the entry endpoint to the full body outcome. *)
val runtime_body_endpoint_tac =
  `LENGTH tx.args = LENGTH args` by
    (drule bind_arguments_length >> simp[]) >>
  qpat_x_assum `runtime_entry_endpoint _ _ _ _ _ _ _ _ _ _ _`
    (qx_choosel_then [`lbl`, `cenv_ext`, `cenv0`, `pos_args`, `min_cds`,
       `is_payable`, `nkey`, `ut'`, `iv`, `rt`, `st`, `cenv`, `sa`, `st'`,
       `func`, `s0`, `G0`, `tn0`]
       (MAP_EVERY ASSUME_TAC o CONJUNCTS) o
     REWRITE_RULE [runtime_entry_endpoint_def]) >>
  `cenv0 = cenv_ext` by
    (qpat_x_assum `(_ /\ runtime_selected_body_start _ _ _ _) \/ _`
       (DISJ_CASES_THEN2 (ACCEPT_TAC o CONJUNCT1)
          (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
      qpat_x_assum `runtime_fallback_body_start _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [runtime_fallback_body_start_def]) >>
      `FST (SND (SND (classify_functions tops))) = SOME fb` by
        (qpat_assum `classify_functions tops = _` (fn th => simp[th])) >>
      drule_all classified_fallback_source_alignment_nr >>
      disch_then SUBST_ALL_TAC >>
      gvs[] >>
      drule_all same_source_fallback_package_environment >>
      disch_then ACCEPT_TAC) >>
  `runtime_entry_body_start tops rpolicy
     (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,
      subst_consts_stmts (module_consts_env tops []) fbody,rt) st` by
    (pure_rewrite_tac[runtime_entry_body_start_def] >>
     qpat_x_assum `(_ /\ runtime_selected_body_start _ _ _ _) \/ _`
       (DISJ_CASES_THEN2
         (fn th => disj1_tac >> ACCEPT_TAC (CONJUNCT2 th))
         (fn th => disj2_tac >> ACCEPT_TAC (List.last (CONJUNCTS th))))) >>
  qpat_x_assum `(_ /\ runtime_selected_body_start _ _ _ _) \/ _` kall_tac >>
  qpat_x_assum `cenv0 = cenv_ext` (SUBST_ALL_TAC o SYM);

val runtime_compiled_body_abi_targets_tac =
  `!tgt. supported_stmts_expr_exists (expr_abi_decode_target_root tgt)
       (subst_consts_stmts (module_consts_env tops []) fbody) ==>
       occurs_abi_decode_target tgt tops` by
    (rpt strip_tac >>
     fs[source_typing_ok_def] >>
     `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
     drule_all checked_const_substitution_abi_decode_target >>
     disch_tac >>
     drule lookup_function_abi_decode_target_occurs >>
     disch_then (qspec_then `tgt` match_mp_tac) >>
     first_assum ACCEPT_TAC);

(* run_lowering's old endpoint (nr = F, no defaults) is a post-binding one. *)
Theorem runtime_entry_endpoint_body_endpoint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody) ==>
    runtime_body_endpoint tops rpolicy unit am tx vs es0 mut F args [] ret
      (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  rpt gen_tac >> strip_tac >>
  runtime_body_endpoint_tac >>
  drule_at_then (Pat `set_external_package_target _ _ = _`)
    drule_all external_source_body_frame >> strip_tac >>
  `nkey = global_nonreentrant_slot /\ ut' = T /\ iv = (mut = View) /\
   rt = (if ret = NoneT then NONE else SOME ret)` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> simp[]) >>
  drule compile_register_positional_args_cenv >> strip_tac >>
  `cenv with ce_vars := cenv0.ce_vars = cenv0` by
    fs[compile_env_component_equality] >>
  mp_tac (Q.SPECL [`tops`, `rpolicy`, `unit`, `lbl`, `cenv0`, `pos_args`,
      `min_cds`, `is_payable`, `F`, `nkey`, `ut'`, `iv`,
      `subst_consts_stmts (module_consts_env tops []) fbody`, `rt`, `st`,
      `cenv`, `sa`, `sa`, `st'`]
    runtime_entry_body_shadow_with_shadow_nr) >>
  disch_then (qspecl_then [`bindings`, `unit.cu_context`,
    `initial_evaluation_context am.sources am.layouts tx NONE`, `env_t`, `env'`,
    `ret`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[comp_return_def])) >>
  disch_then (qx_choosel_then [`func2`, `shadow_ctx`, `shadow_func`, `cenv'`,
    `sb`, `shadow_sl`, `shadow_sb`, `shadow_unit`, `shadow_sa`, `shadow_st'`]
    strip_assume_tac) >>
  `func2 = func` by gvs[] >>
  `es0.storage_trace = []` by
    (drule send_call_value_accounts >> simp[initial_state_def]) >>
  `storage_trace_domain
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) es0.storage_trace` by
    simp[storage_trace_domain_def, valid_horizon_def, storage_trace_horizon_def,
         storage_observations_ok_def, storage_trace_regions_def,
         storage_trace_locks_def, regions_consistent_def, storage_locks_separated_def,
         storage_well_formed_on_def, storage_roots_fit_def,
         storage_trace_backends_well_formed_def] >>
  drule_all external_entry_bound_no_defaults >> strip_tac >>
  PURE_REWRITE_TAC [runtime_body_endpoint_def] >>
  qexistsl_tac [`[]`,`cenv0`,`cenv`,`sa`,`st'`,`func`,`s0`,`G0`,`tn0`,
    `shadow_unit`,`shadow_func`,`shadow_sa`,`shadow_st'`] >>
  gvs[] >> rpt conj_tac
  >- (qexistsl_tac [`bindings`, `env_t`, `env'`] >> simp[]) >>
  metis_tac[]
QED

val runtime_shadow_body_inv_tac =
  qpat_assum `source_typing_ok tops am tx` (fn typing =>
    assume_tac (MATCH_MP source_typing_ok_vtype_keys_distinct typing)) >>
  drule_all runtime_shadow_body_inv >> strip_tac;

Theorem runtime_selected_body_loop_calls[local]:
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  (!vis mut nr raw fn args dflts ret stmts.
     MEM (FunctionDecl vis mut nr raw fn args dflts ret stmts) tops ==>
     stmts_loop_calls_ok [(NONE,tops)] stmts) /\
  stmts_loop_calls_ok [(NONE,tops)]
    (subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  strip_tac >>
  `?art A. check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
      constants_fold_module [(NONE,tops)] (account_immutables am tx.target)
        NONE tops FEMPTY = SOME A` by fs[source_typing_ok_def] >>
  pop_assum strip_assume_tac >>
  drule bodyLoopCallsTheory.checked_module_loop_calls_ok >> disch_then assume_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `stmts_loop_calls_ok [(NONE,tops)] fbody` by
    (drule_all_then ACCEPT_TAC bodyLoopCallsTheory.checked_external_body_loop_calls_ok) >>
  drule_all_then ACCEPT_TAC bodyLoopCallsTheory.checked_subst_consts_loop_calls_ok
QED

Theorem runtime_selected_body_frag_full[local]:
  !am tx mut nr args dflts fbody os gs es0 DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    cx = initial_evaluation_context am.sources am.layouts tx NONE /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret_ty,fbody) /\
    external_entry_bound tops am tx os gs mut args dflts es0 /\
    lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es) /\
    ss = subst_consts_stmts (module_consts_env tops []) fbody /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
    supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_selected_body_loop_calls >> strip_tac >>
  qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,`shadow_ctx`,
    `func`,`shadow_func`,`cenv`,`cx`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,
    `ss`,`es`] mp_tac body_stmts_sim_full >>
  asm_rewrite_tac[]
QED

Theorem runtime_selected_body_internal_constant_defaults:
  !am tx mut nr args dflts fbody os gs es0 DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    internal_defaults_const_names tops /\
    cx = initial_evaluation_context am.sources am.layouts tx NONE /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret_ty,fbody) /\
    external_entry_bound tops am tx os gs mut args dflts es0 /\
    lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es) /\
    ss = subst_consts_stmts (module_consts_env tops []) fbody /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
    supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  rpt gen_tac >> strip_tac >>
  `~cx.in_deploy` by simp[initial_evaluation_context_def] >>
  `?rpolicy unit. lower_vyper_runtime_unit tops rpolicy = SOME unit` by
    (drule bodySimTheory.body_inv_contract >>
     simp[bodyInvSplitTheory.contract_inv_def,
          compileUnitTheory.lower_vyper_runtime_unit_mods_singleton] >>
     metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `env_context_consistent env cx` by fs[expr_sim_inv_def, env_consistent_def] >>
  `es.immutables = am.immutables` by
    (drule_all external_entry_bound_source_frame >> strip_tac >>
     drule_all_then strip_assume_tac external_body_lock_frame >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env es` by
    (qpat_x_assum `cx = initial_evaluation_context _ _ _ _` SUBST_ALL_TAC >>
     drule_all_then ACCEPT_TAC external_source_body_const_cells_checked) >>
  qspecl_then [`am`,`tx`,`mut`,`nr`,`args`,`dflts`,`fbody`,`os`,`gs`,`es0`,
    `DF`,`lo`,`d`,`PG`,`tops`,`bindings`,`ctx`,`shadow_ctx`,`func`,
    `shadow_func`,`cenv`,`cx`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`ss`,`es`]
    mp_tac runtime_selected_body_frag_full >>
  asm_rewrite_tac[]
QED

fun runtime_selected_body_frag_tac nr defaults readings endpoint =
  qpat_assum `frame_ret_ok_full _ _ _ _ _` (fn frame_th =>
    let
      val (_, [frame, cx, retq, cenv, ret]) = strip_comb (concl frame_th)
      val [df, lo, d, ctx, shadow_ctx, pg, func, shadow_func] =
        map (fn tm => [ANTIQUOTE tm]) (pairSyntax.strip_pair frame)
    in
      qspecl_then
        [`am`, `tx`, `mut`, nr, `args`, defaults, `fbody`, `vs.vs_outcomes`,
         readings, `es0`,
         df, lo, d, pg, `tops`, `bindings`, ctx, shadow_ctx, func, shadow_func,
         [ANTIQUOTE cenv], [ANTIQUOTE cx], `env_t`, `env'`, [ANTIQUOTE ret],
         `NoLoop`, [ANTIQUOTE retq], `compiled_body`, endpoint]
        mp_tac runtime_selected_body_frag_full
    end) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      fs[Abbr `cx`, Abbr `compiled_body`]);

val runtime_plain_entry_bound_tac =
  drule_all external_entry_bound_no_defaults >> strip_tac >>
  `external_entry_bound tops am tx vs.vs_outcomes es0.gas_obs mut args [] es0` by
    (qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
       (qspec_then `es0.gas_obs` mp_tac) >>
     simp[evaluation_state_component_equality]);

val runtime_entry_horizon_simp =
  simp[valid_horizon_def, storage_trace_horizon_def, storage_trace_regions_def,
       storage_trace_locks_def, regions_consistent_def, storage_locks_separated_def,
       storage_well_formed_on_def, storage_observations_ok_def, storage_roots_fit_def,
       storage_trace_backends_well_formed_def, arithmeticTheory.ADD1];

val runtime_empty_trace_tac =
  `es0.storage_trace = []` by
    (drule send_call_value_accounts >> simp[initial_state_def]);

val runtime_lock_trace_tac =
  runtime_empty_trace_tac >>
  `es_lock.storage_trace = [StorageLock global_nonreentrant_slot]` by
    (drule_all lock_if_nr_success_trace >> simp[]);

fun runtime_entry_allocas_tac endpoint =
  qpat_assum `!st0 H. valid_horizon _ _ H ^endpoint ==> _`
    (qspecl_then [`initial_state am []`, `storage_trace_horizon ^endpoint`] mp_tac) >>
  impl_tac >- runtime_entry_horizon_simp >>
  strip_tac >>
  qpat_assum `stmt_state_rel _ unit.cu_context func cenv _ _ s0`
    (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  simp[];

Theorem runtime_body_reached_dalloca_headroom[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  gas_path unit.cu_context func
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>) n (OK s0) /\
  (ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s) ==>
  !fn inst s. frag_reachable unit.cu_context func s0 fn inst s ==>
    dalloca_fmp_headroom inst s
Proof
  strip_tac >>
  Cases_on `ctx_has_dalloca unit.cu_context`
  >- (`!bb label. lookup_block label func.fn_blocks = SOME bb ==>
         phi_prefix_length bb.bb_instructions = 0` by
        (rpt strip_tac >> drule_all lower_vyper_runtime_unit_block_phi >> simp[]) >>
      `?bb. lookup_block "__entry" func.fn_blocks = SOME bb` by
        (Cases_on `func.fn_blocks` >>
         fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
      qabbrev_tac `entry = vs with <|vs_prev_bb := NONE;
        vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
      `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
      `enters_block func entry entry` by
        simp[enters_block_def, Abbr `entry`, eval_phis_no_phi, venom_state_fupdfupds] >>
      `!i. active_inst func i entry ==> raw_reachable vs unit.cu_context func i entry` by
        (rpt strip_tac >> irule raw_reachable_entry >> fs[Abbr `entry`]) >>
      `!i. active_inst func i s0 ==> raw_reachable vs unit.cu_context func i s0` by
        (rpt strip_tac >>
         qpat_assum `gas_path _ _ entry n (OK s0)` (fn path =>
           irule raw_reachable_gas_path >> irule_at Any path >> simp[] >>
           first_assum ACCEPT_TAC)) >>
      rpt strip_tac >>
      `raw_reachable vs unit.cu_context fn inst s` by
        (drule raw_reachable_through_fragment >>
         disch_then (qspec_then `vs` irule) >> first_assum ACCEPT_TAC) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `MEM func unit.cu_context.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule_then drule frag_reachable_members >> strip_tac >>
  `inst.inst_opcode <> DALLOCA` by
    (fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  simp[dalloca_fmp_headroom_def]
QED

val runtime_reached_headroom_tac =
  `!fn inst s. frag_reachable unit.cu_context func s0 fn inst s ==>
     dalloca_fmp_headroom inst s` by (
  mp_tac (Q.INST
    [`tops` |-> `tops`, `rpolicy` |-> `rpolicy`, `unit` |-> `unit`,
     `func` |-> `func`, `vs` |-> `vs`, `s0` |-> `s0`, `n` |-> `0:num`]
    runtime_body_reached_dalloca_headroom) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC);

(* Compose at the body's marks, optionally retaining a call-result fact. *)
fun runtime_body_compose_from_tac compose readings marks =
  drule_at_then (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    (Q.ISPECL_THEN
      [`vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0 |>`,
       readings,
       `\(H : (bool # bytes32 # type_value) list # num list) c r.
          external_call_result_rel H tops ret tx c r`,
       `source_exempt tops :
          ((value + exception) # abstract_machine # call_request list) -> bool`,
       marks]
      (fn th => mp_tac (SIMP_RULE (srw_ss()) [] th))) compose;

fun runtime_body_compose_tac compose =
  runtime_body_compose_from_tac compose
    `\g. call_external_trace (SOME vs.vs_outcomes) g am tx` `[]:bool list`;

val runtime_compose_exit_tac =
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
     fbody (es0 with gas_obs := gx) = (res, ee with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_stmts _ compiled_body _ = (_,_)`
       (qspec_then `[]` mp_tac) >>
         qpat_assum `!gx. eval_stmts _ compiled_body _ = _` (fn th => simp[th])) >>
  `stmt_res_ok NoLoop res` by
    (drule_all external_body_source_ok >> simp[]) >>
  drule_all selected_call_trace_body >> strip_tac >>
  qpat_x_assum `!tail. stmt_exit_ptr _ _ _ _ _`
    (qspec_then `[]` mp_tac) >>
  simp[stmt_exit_ptr_def] >> strip_tac;

val runtime_compose_abort_halt_cases_tac =
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `stmt_res_ok _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_res_ok_def]) >>
  gvs[] >> Cases_on `r`;

val runtime_compose_halt_tac =
  fs[halt_exit_def] >>
  drule external_halt_rel_success >>
  disch_then (qspecl_then
    [`cx_tops (initial_evaluation_context am.sources am.layouts tx NONE)`,
     `tx`, `am.sources`, `am.exports`, `am.layouts`] mp_tac) >>
  simp[initial_evaluation_context_def, finalize_pending_deletions_def];

Theorem eval_stmts_missing_gas_reading_empty:
  !cx body st st'.
    eval_stmts cx body st =
      (INR (Error (RuntimeError "msg.gas: no gas reading")), st') ==>
    st'.gas_obs = []
Proof
  ACCEPT_TAC (cj 2 evaluate_missing_reading_state)
QED

(* A nonempty unread tail rules out the missing-reading error in the body.
   The selected-call wrapper either forwards the body exception or produces
   a different result (including TypeError on a failed return conversion). *)
fun runtime_selected_readings_finish_tac (marks_tac, unpack_tac) =
  disch_then (qx_choose_then `marks` assume_tac) >>
  marks_tac >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[call_external_trace_observations] >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choosel_then [`cr`, `am'`, `rqs`, `obs`]
      (MAP_EVERY ASSUME_TAC o CONJUNCTS)))
  >- (`!tail. ~call_storage_ok am tx vs.vs_outcomes
           (gas_explicit marks vs.vs_gas_readings ++ tail)` by
        (gen_tac >> strip_tac >>
         drule source_storage_guards_domain >> simp[]) >>
      conj_tac
      >- (unpack_tac >>
          pure_rewrite_tac[source_unit_execution_correct_with_def] >>
          qexistsl_tac [`func`, `shadow_func`] >> simp[] >> metis_tac[]) >>
      simp[]) >>
  conj_tac
  >- (unpack_tac >>
      pure_rewrite_tac[source_unit_execution_correct_with_def] >>
      qexistsl_tac [`func`, `shadow_func`] >> simp[] >>
      disj2_tac >> qexistsl_tac [`cr`, `am'`, `rqs`, `obs`] >> simp[]) >>
  disch_tac >> qx_gen_tac `unread` >>
  qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `unread` (strip_assume_tac o MATCH_MP call_external_trace_result)) >>
  simp[];

Theorem external_lock_failure_trace[local]:
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,dflts,ret,fbody) /\
  (!gx. external_entry_bound tops am tx os (prefix ++ gx) mut args dflts
    (es0 with gas_obs := gx)) /\
  lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
    T (is_view_mut mut) es0 = (INR exc,es_abort) ==>
  !gx. call_external_trace (SOME os) (prefix ++ gx) am tx =
    (INR exc,am,es_abort.requests,es_abort.storage_trace)
Proof
  strip_tac >> drule_all call_external_selected_lock_failure >>
  disch_then ACCEPT_TAC
QED

Theorem runtime_lock_abort_result_with:
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,dflts,ret,fbody) /\
  (!gx. external_entry_bound tops am tx vs.vs_outcomes
    (gas_explicit marks0 vs.vs_gas_readings ++ gx) mut args dflts
    (es0 with gas_obs := gx)) /\
  lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
    T (is_view_mut mut) es0 = (INR exc,es_abort) /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  gas_shadow_context unit.cu_context shadow_unit.cu_context /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions =
    SOME func /\
  fn_entry_label func = SOME "__entry" /\
  lookup_block "__entry" func.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 /\
  expr_exit (INR exc : unit + exception) (Abort a t) /\
  (exc = Error (RuntimeError "nonreentrant lock") \/
   exc = Error (RuntimeError "write in static context")) /\
  (!D. gas_origin_ptr_path
     (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
      unit.cu_context,func,[])
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>,FEMPTY,entry_taint) marks0 (OK s0,G0,tn0)) /\
  (!D. gas_origin_ptr_path
     (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
      unit.cu_context,func,[])
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>,FEMPTY,entry_taint) marks0 (Abort a t,G,tn)) ==>
  source_unit_execution_correct_with shadow_unit.cu_context marks0 tops ret am tx unit vs /\
  (!tail. FST (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks0 vs.vs_gas_readings ++ tail) am tx) <>
    INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule_all external_lock_failure_trace >> strip_tac >>
  reverse conj_tac
  >- (gen_tac >>
      qpat_x_assum `!gx. call_external_trace _ _ _ _ = _`
        (qspec_then `tail` (mp_tac o MATCH_MP call_external_trace_result)) >>
      Cases_on `exc = Error (RuntimeError "nonreentrant lock")` >> gvs[]) >>
  `OPTREL gas_shadow_function (SOME func)
    (lookup_function "__entry" shadow_unit.cu_context.ctx_functions)` by
    (qpat_assum `lookup_function "__entry" unit.cu_context.ctx_functions = SOME func`
       (SUBST1_TAC o SYM) >>
     irule gas_shadow_lookup_function >> fs[gas_shadow_context_def]) >>
  Cases_on `lookup_function "__entry" shadow_unit.cu_context.ctx_functions`
  >- fs[optionTheory.OPTREL_def] >>
  qpat_x_assum `OPTREL gas_shadow_function _ _`
    (ASSUME_TAC o SIMP_RULE (srw_ss()) [optionTheory.OPTREL_def]) >>
  rename1 `gas_shadow_function func shadow_fn` >>
  `MEM func unit.cu_context.ctx_functions /\
    MEM shadow_fn shadow_unit.cu_context.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  qabbrev_tac `entry = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  PURE_REWRITE_TAC [source_unit_execution_correct_with_def] >>
  qexistsl_tac [`func`,`shadow_fn`] >>
  qpat_assum `Abbrev (entry = _)`
    (fn th => ASM_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  reverse (Cases_on `storage_trace_domain
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) es_abort.storage_trace`)
  >- (disj1_tac >> conj_tac
      >- (gen_tac >> strip_tac >> drule source_storage_guards_domain >>
          simp[GSYM call_external_trace_observations]) >>
      qexistsl_tac [`ARB:(bool # bytes32 # type_value) list # num list`,
        `func`, `[]`, `G0`, `tn0`, `s0`] >>
      irule (cj 1 gas_origin_ptr_focus_rules) >> simp[]) >>
  disj2_tac >> qexistsl_tac
    [`INR exc`, `am`, `es_abort.requests`, `es_abort.storage_trace`] >>
  simp[] >> disj2_tac >> qexists_tac `Abort a t` >>
  simp[exit_result_def] >>
  conj_tac >-
    (qpat_assum `!D. gas_origin_ptr_path _ (entry,_,_) _ (Abort _ _,_,_)`
       (mp_tac o CONJUNCT1 o MATCH_MP gas_origin_ptr_path_projections o Q.SPEC `ARB:dead`) >>
     simp[Abbr `entry`]) >>
  rpt gen_tac >> strip_tac >>
  conj_tac >-
    (qpat_assum `exc = _ \/ exc = _` (DISJ_CASES_THEN SUBST1_TAC) >>
     simp[external_call_result_rel_def]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (entry,_,_) _ (Abort _ _,_,_)`
    (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec o Q.SPEC
      `cx_dead (H : (bool # bytes32 # type_value) list # num list)
         (initial_evaluation_context am.sources am.layouts tx NONE)`) >>
  simp[exit_result_def] >> disch_then (qx_choose_then `fuel` strip_assume_tac) >>
  `eval_phis entry bb.bb_instructions = OK entry` by
    simp[eval_phis_no_phi] >>
  `entry with vs_inst_idx := 0 = entry` by simp[Abbr `entry`] >>
  `lookup_block entry.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `entry`] >>
  `run_blocks (SUC fuel) unit.cu_context func entry = Abort a t` by
    (qspecl_then [`fuel`,`unit.cu_context`,`func`,`entry`,`bb`] mp_tac
       run_blocks_run_from_no_phi >> asm_rewrite_tac[]) >>
  irule ptrSafeRunTheory.ptr_safe_blocks_all_fuel >> qexists_tac `SUC fuel` >>
  simp[] >>
  qspecl_then [`cx_dead (H : (bool # bytes32 # type_value) list # num list)
       (initial_evaluation_context am.sources am.layouts tx NONE)`,
    `0`,`fuel`,`unit.cu_context`,`func`,`[]`,`FEMPTY`,`entry_taint`,
    `entry`,`bb`,`entry`] mp_tac ptrSafeRunTheory.ptr_safe_blocks_block >>
  asm_rewrite_tac[] >> disch_then SUBST1_TAC >>
  qpat_assum `lookup_block entry.vs_current_bb func.fn_blocks = SOME bb`
    (fn th => qpat_assum `ptr_safe_run _ _ _ _ _ _ _ _ _`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [ptrSafeRunTheory.ptr_safe_run_def,th]))
QED

Triviality runtime_package_source_body:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,subst_consts_stmts E source_body)) =
    (lbl,ce,pos_args,min_cds,pay,nr',key,tr,view,
     subst_consts_stmts E source_body,rt) ==>
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,source_body)) =
    (lbl,ce,pos_args,min_cds,pay,nr',key,tr,view,source_body,rt)
Proof
  simp[package_external_fn_def, set_external_package_target_def,
       build_compile_env_subst_consts_stmts] >>
  strip_tac >> gvs[]
QED

Theorem runtime_lock_expr_sim_inv[local]:
  lock_if_nr cx nr iv es = (INL (),es_lock) /\ expr_sim_inv cenv cx env es ==>
  expr_sim_inv cenv cx env es_lock
Proof
  strip_tac >> drule external_body_lock_frame >> strip_tac >>
  qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
  asm_simp_tac pure_ss [expr_sim_inv_def, state_well_typed_def, env_consistent_def,
    env_scopes_consistent_def, env_immutables_consistent_def] >> disch_then ACCEPT_TAC
QED

val runtime_bound_frame_tac =
  `external_entry_bound tops am tx vs.vs_outcomes (prefix ++ es0.gas_obs)
     mut args dflts es0` by
    (`es0 with gas_obs := es0.gas_obs = es0` by (Cases_on `es0` >> simp[]) >>
     pop_assum (fn same =>
       qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
         (qspec_then `es0.gas_obs` (ACCEPT_TAC o PURE_REWRITE_RULE [same])))) >>
  runtime_compiled_body_abi_targets_tac >>
  rename1 `set_external_package_target _ _ =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,compiled_body,rt)` >>
  `nkey = global_nonreentrant_slot /\ ut' = T /\ iv = (mut = View) /\
   rt = (if ret = NoneT then NONE else SOME ret)` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> simp[]) >>
  qpat_assum `Abbrev (compiled_body = _)` (fn eq =>
    qpat_assum `set_external_package_target _ _ = _`
      (assume_tac o MATCH_MP runtime_package_source_body o
       PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq]));

Theorem runtime_bound_lock_outside_domain[local]:
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  (!gx. external_entry_bound tops am tx os (prefix ++ gx) mut args dflts
    (es0 with gas_obs := gx)) /\
  lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
  (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
  ~storage_trace_domain cx (initial_state am []) es_lock.storage_trace ==>
  !tail. ~call_storage_ok am tx os (prefix ++ tail)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  drule source_storage_guards_domain >>
  qpat_x_assum `cx = _` (fn eq => PURE_REWRITE_TAC [GSYM eq] >>
    SUBST_ALL_TAC eq) >>
  Cases_on `eval_stmts
    (initial_evaluation_context am.sources am.layouts tx NONE)
    fbody (es_lock with gas_obs := tail)` >>
  rename1 `_ = (res,ee)` >>
  `?eu.
     unlock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
       nr (is_view_mut mut) ee = (INL (),eu) /\
     ?extra. eu.storage_trace = ee.storage_trace ++ extra` by
    (reverse (Cases_on `nr`) >-
       (qexists_tac `ee` >> simp[unlock_if_nr_def, return_def] >>
        qexists_tac `[]` >> simp[]) >>
     mp_tac (Q.INST [`nr` |-> `T`, `iv` |-> `is_view_mut mut`,
       `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
       `es` |-> `ee`, `key` |-> `global_nonreentrant_slot`]
       (SPEC_ALL unlock_if_nr_success_trace)) >>
     impl_tac >- fs[] >> strip_tac >> qexists_tac `se` >> simp[] >>
     qexists_tac `if is_view_mut mut then []
       else [StorageLock global_nonreentrant_slot]` >> simp[]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
    (qspec_then `tail` assume_tac) >>
  drule_all selected_call_trace_result_nr >> strip_tac >>
  `?extra. ee.storage_trace = es_lock.storage_trace ++ extra` by
    (qpat_assum `eval_stmts _ fbody _ = (res,ee)`
       (mp_then (Pat `f st = _`) mp_tac storage_trace_frame_prefix) >>
     simp[evaluate_storage_trace_frame]) >>
  qpat_assum `call_external_trace _ _ _ _ = _`
    (fn th => PURE_REWRITE_TAC [GSYM call_external_trace_observations,th,pairTheory.SND]) >>
  Cases_on `res = INL () \/ (?v. res = INR (ReturnException v))` >>
  fs[] >> metis_tac[storage_trace_domain_prefix]
QED

val runtime_locked_eval_tac =
  `eval_stmts cx fbody (es_lock with gas_obs := gx) =
     (res, ee with gas_obs := [])` by
    (qpat_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
       (qspec_then `[]` (fn eval =>
         qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _`
           (qspec_then `gx` (fn subst => ACCEPT_TAC
              (PURE_REWRITE_RULE [subst] (REWRITE_RULE [APPEND_NIL] eval))))))) >>
  `stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)` by
    (qpat_assum `Abbrev (cx = _)` (fn eq =>
      mp_tac (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]
        (Q.SPECL [`tops`,`am`,`tx`,`ret`,`vs.vs_outcomes`,`mut`,`nr`,
          `args`,`dflts`,`fbody`,`prefix ++ es0.gas_obs`,`es0`,`es_lock`,`gx`,
          `res`,`ee with gas_obs := []`] external_body_source_ok_nr))) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC);

fun runtime_bound_unlock_tac return_type gas result state =
  let val state_tm = Parse.Term state in
  `?eu. unlock_if_nr cx nr (is_view_mut mut) ^state_tm = (INL (),eu)` by
    (Cases_on `nr`
     >- (`cx.nonreentrant_slot = SOME global_nonreentrant_slot` by fs[] >>
         mp_tac (Q.INST [`nr` |-> `T`, `iv` |-> `is_view_mut mut`,
           `cx` |-> `cx`, `es` |-> state, `key` |-> `global_nonreentrant_slot`]
             (SPEC_ALL unlock_if_nr_success_trace)) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         disch_then (qx_choose_then `se` (fn th =>
           qexists_tac `se` >> ACCEPT_TAC (CONJUNCT1 th)))) >>
     simp[unlock_if_nr_def, return_def]) >>
  rename1 `unlock_if_nr cx nr (is_view_mut mut) ^state_tm = (INL (),eu)` >>
  qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
    (qspec_then gas assume_tac) >>
  qpat_assum `Abbrev (cx = _)` (fn eq =>
    mp_tac (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]
      (Q.SPECL [`tops`,`am`,`tx`,return_type,`mut`,`nr`,`args`,`dflts`,`fbody`,
        `vs.vs_outcomes`,`prefix`,gas,`es0`,`es_lock`,result,state,`eu`]
        selected_call_trace_result_nr))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac
  end;

(* The registration cursor survives an early lock failure.  On success the
   raw and shadow cursors and the ghost pair are fixed before any horizon
   is chosen.  In particular the success arm is usable before running the
   body, not just when the whole body has a simulated outcome. *)
Theorem runtime_body_endpoint_prepare_with_cases:
  !L tops rpolicy unit am tx ret vs mut nr args dflts fbody es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    runtime_body_endpoint_with L tops rpolicy unit am tx vs es0 mut nr args dflts ret
      (subst_consts_stmts (module_consts_env tops []) fbody) /\
    (!a b c d. cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ L a d ==>
       L b c) ==>
    (?shadow_unit marks0 func sa st' cenv s0 G0 tn0 exc es_abort a t G tn.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      nr /\
      (initial_evaluation_context am.sources am.layouts tx NONE).nonreentrant_slot =
         SOME global_nonreentrant_slot /\
      is_view_mut mut = (mut = View) /\
      lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
        nr (is_view_mut mut) es0 = (INR exc,es_abort) /\
      compile_guarded_body cenv T global_nonreentrant_slot T (mut = View)
        (subst_consts_stmts (module_consts_env tops []) fbody)
        (if ret = NoneT then NONE else SOME ret) sa = ((),st') /\
      fn_has_code sa st' func /\
      s0.vs_gas_readings = DROP (LENGTH marks0) vs.vs_gas_readings /\
      (!H : (bool # bytes32 # type_value) list # num list.
         stmt_state_rel H unit.cu_context func cenv
           (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
         ghost_inv H NONE cenv
           (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0) /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      fn_entry_label func = SOME "__entry" /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      ~s0.vs_halted /\
      expr_exit (INR exc : unit + exception) (Abort a t) /\
      (exc = Error (RuntimeError "nonreentrant lock") \/
       exc = Error (RuntimeError "write in static context")) /\
      (!D. gas_origin_ptr_path
         (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
          unit.cu_context,func,[])
         (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>,FEMPTY,entry_taint)
         marks0 (OK s0,G0,tn0) /\
           gas_origin_ptr_path
         (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
          unit.cu_context,func,[])
         (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>,FEMPTY,entry_taint)
         marks0 (Abort a t,G,tn)) /\
      source_unit_execution_correct_with shadow_unit.cu_context marks0
        tops ret am tx unit vs /\
      (!tail. FST (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks0 vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading")))) \/
    (?shadow_unit marks0 es_lock.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
        nr (is_view_mut mut) es0 = (INL (),es_lock) /\
      ~storage_trace_domain (initial_evaluation_context am.sources am.layouts tx NONE)
        (initial_state am []) es_lock.storage_trace /\
      (!tail. ~call_storage_ok am tx vs.vs_outcomes
          (gas_explicit marks0 vs.vs_gas_readings ++ tail)) /\
      source_unit_execution_correct_with shadow_unit.cu_context marks0
        tops ret am tx unit vs) \/
    (?cx compiled_body entry explicit prefix marks0 shadow_unit func shadow_func
      cenv cenv' bindings env_t env' es_lock sa sl sb st' shadow_sl shadow_sb
      s_b G_b tn_b.
      cx = initial_evaluation_context am.sources am.layouts tx NONE /\
      compiled_body = subst_consts_stmts (module_consts_env tops []) fbody /\
      entry = (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                          vs_inst_idx := 0|>) /\
      explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context /\
      prefix = gas_explicit marks0 vs.vs_gas_readings /\
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      (!gx. external_entry_bound tops am tx vs.vs_outcomes (prefix ++ gx)
        mut args dflts (es0 with gas_obs := gx)) /\
      external_entry_bound tops am tx vs.vs_outcomes (prefix ++ es0.gas_obs)
        mut args dflts es0 /\
      lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
      (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
              is_view_mut mut = (mut = View)) /\
      global_nonreentrant_slot < dimword (:256) /\
      (nr /\ mut <> View ==> ~tx.is_static) /\
      (!gas. eval_stmts cx compiled_body (es_lock with gas_obs := gas) =
             eval_stmts cx fbody (es_lock with gas_obs := gas)) /\
      storage_trace_domain cx (initial_state am []) es_lock.storage_trace /\
      body_inv tops unit.cu_context cenv cx /\
      shadow_body_inv tops unit.cu_context shadow_unit.cu_context /\
      struct_args_unique tops /\
      supported_stmts tops bindings compiled_body /\
      (!vis mut nr raw fn args dflts ret stmts.
        MEM (FunctionDecl vis mut nr raw fn args dflts ret stmts) tops ==>
        stmts_loop_calls_ok [(NONE,tops)] stmts) /\
      stmts_loop_calls_ok [(NONE,tops)] compiled_body /\
      (!tgt. supported_stmts_expr_exists (expr_abi_decode_target_root tgt)
         compiled_body ==> occurs_abi_decode_target tgt tops) /\
      body_const_cells_agree [(NONE,tops)] cx env_t es_lock /\
      expr_sim_inv cenv cx env_t es_lock /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret compiled_body = SOME env' /\
      stmts_exprs_ok cenv compiled_body /\
      call_evaluation_safe cx (int_calls_stmts compiled_body) /\
      frame_ret_ok_full
        ((\H. cx_dead H cx),0,NONE,unit.cu_context,shadow_unit.cu_context,[],func,shadow_func)
        cx
        (\H v ee gt r. ?tv v' us.
           evaluate_type (type_env tops) ret = SOME tv /\
           safe_cast tv v = SOME v' /\
           unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
           external_call_result_rel H tops ret tx
             (INL v', finalize_pending_deletions
                (abstract_machine_from_state am.sources am.exports am.layouts us),
              us.requests) r)
        cenv ret /\
      compile_guarded_body cenv nr global_nonreentrant_slot T (mut = View)
        compiled_body (if ret = NoneT then NONE else SOME ret) sa = ((),st') /\
      (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
       else comp_return ()) sa = ((),sl) /\
      compile_stmts cenv NoLoop
        (case (if ret = NoneT then NONE else SOME ret) of
           NONE => BaseT BoolT | SOME ty => ty) compiled_body sl = ((),sb) /\
      stmts_env cenv NoLoop ret compiled_body sl = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body)
        shadow_sl = (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sl shadow_sl /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context unit.cu_context shadow_unit.cu_context /\
      ctx_inst_ids_distinct unit.cu_context /\ gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_unit.cu_context.ctx_functions /\
      fn_has_code sl sb func /\ fn_has_code shadow_sl shadow_sb shadow_func /\
      fn_has_code sb st' func /\ fn_inst_ids_distinct func /\
      cx_tops cx = tops /\ ~cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
      cenv.ce_ctor_exit_label = NONE /\ L sl sb /\
      gas_path_mem unit.cu_context func entry (LENGTH marks0) (OK s_b) /\
      alloca_history func s_b /\ return_buf_frame NONE cenv sl s_b /\
      local_ptrs_reserved cenv sl /\ ~block_is_terminated sl /\
      ~s_b.vs_halted /\ s_b.vs_current_bb = sl.cs_current_bb /\
      s_b.vs_inst_idx = LENGTH sl.cs_current_insts /\
      s_b.vs_gas_readings = DROP (LENGTH marks0) vs.vs_gas_readings /\
      s_b.vs_code = vs.vs_code /\ s_b.vs_labels = vs.vs_labels /\
      (!fn inst s. frag_reachable unit.cu_context func s_b fn inst s ==>
        dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
        storage_well_formed_on cx es_lock (FST H)) /\
      !H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
        stmt_state_rel H unit.cu_context func cenv cx es_lock s_b /\
        ghost_inv_at (cx_dead H cx) 0 NONE cenv cx es_lock G_b tn_b s_b /\
        gas_origin_ptr_path (cx_dead H cx,0,explicit,unit.cu_context,func,[])
          (entry,FEMPTY,entry_taint) marks0 (OK s_b,G_b,tn_b) /\
        ((!fuel. ptr_safe_run (cx_dead H cx) 0 fuel
                  unit.cu_context func [] G_b tn_b s_b) ==>
         !fuel. ptr_safe_blocks (cx_dead H cx) 0 fuel
           unit.cu_context func [] FEMPTY entry_taint entry))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `compiled_body = subst_consts_stmts (module_consts_env tops []) fbody` >>
  qpat_x_assum `runtime_body_endpoint_with _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_body_endpoint_with_def]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  qabbrev_tac `entry = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  qabbrev_tac `explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context` >>
  qabbrev_tac `prefix = gas_explicit marks0 vs.vs_gas_readings` >>
  `cenv.ce_ctor_exit_label = NONE` by
    (qpat_assum `cenv with ce_vars := _ = cenv0`
       (mp_tac o AP_TERM ``compile_env_ce_ctor_exit_label``) >>
     simp[] >> disch_then SUBST1_TAC >>
     drule return_package_target_inversion >> strip_tac >>
     qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def, update_cenv_nonreentrant_def] >>
     strip_tac >> Cases_on `ret = NoneT` >>
     gvs[update_cenv_ret_abi_def]) >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
           is_view_mut mut = (mut = View)` by
    (strip_tac >> gvs[] >>
     drule_all externalEntryJointTheory.selected_nonreentrant_lock_metadata >>
     simp[Abbr `cx`]) >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[contextTheory.global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) es0` >>
  rename1 `_ = (lock_result,es_lock)` >>
  reverse (Cases_on `lock_result`)
  >- (rename1 `_ = (INR exc,es_lock)` >>
      `nr = T` by (Cases_on `nr` >> fs[lock_if_nr_def, return_def]) >>
      qpat_x_assum `nr = T` SUBST_ALL_TAC >>
      `?bb. lookup_block "__entry" func.fn_blocks = SOME bb /\
            phi_prefix_length bb.bb_instructions = 0` by
        (`?bb. lookup_block "__entry" func.fn_blocks = SOME bb` by
           (Cases_on `func.fn_blocks` >>
            fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
         pop_assum strip_assume_tac >> qexists_tac `bb` >> simp[] >>
         drule_all lower_vyper_runtime_unit_block_phi >> simp[]) >>
      pop_assum strip_assume_tac >>
      `?a s_abort G_abort tn_abort.
        expr_exit (INR exc : unit + exception) (Abort a s_abort) /\
        (exc = Error (RuntimeError "nonreentrant lock") \/
         exc = Error (RuntimeError "write in static context")) /\
        !D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
          (entry,FEMPTY,entry_taint) marks0 (Abort a s_abort,G_abort,tn_abort)` by
        (mp_tac (Q.INST [`cx` |-> `cx`, `ctx` |-> `unit.cu_context`,
           `ss` |-> `entry`, `fbody` |-> `compiled_body`,
           `rt` |-> `if ret = NoneT then NONE else SOME ret`,
           `es_abort` |-> `es_lock`, `marks0` |-> `marks0`,
           `s0` |-> `s0`, `G0` |-> `G0`, `tn0` |-> `tn0`,
           `explicit` |-> `explicit`]
           (SPEC_ALL external_entry_abort_from_registration)) >>
         impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           fs[Abbr `entry`]) >>
         disch_then (qx_choosel_then [`a`,`s`,`G`,`tn`] strip_assume_tac) >>
         qexistsl_tac [`a`,`s`,`G`,`tn`] >> simp[]) >>
      pop_assum strip_assume_tac >>
      disj1_tac >>
      qexistsl_tac [`shadow_unit`,`marks0`,`func`,`sa`,`st'`,`cenv`,`s0`,
        `G0`,`tn0`,`exc`,`es_lock`,`a`,`s_abort`,`G_abort`,`tn_abort`] >>
      `source_unit_execution_correct_with shadow_unit.cu_context marks0
         tops ret am tx unit vs /\
       (!tail. FST (call_external (SOME vs.vs_outcomes)
            (gas_explicit marks0 vs.vs_gas_readings ++ tail) am tx) <>
          INR (Error (RuntimeError "msg.gas: no gas reading")))` by
      (mp_tac (Q.INST [`es_abort` |-> `es_lock`, `t` |-> `s_abort`,
        `G` |-> `G_abort`, `tn` |-> `tn_abort`, `exc` |-> `exc`,
        `s0` |-> `s0`, `G0` |-> `G0`, `tn0` |-> `tn0`,
        `marks0` |-> `marks0`, `a` |-> `a`, `bb` |-> `bb`]
        (SPEC_ALL runtime_lock_abort_result_with)) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          fs[Abbr `cx`, Abbr `explicit`, Abbr `prefix`, Abbr `entry`] >>
          Cases_on `mut` >> gvs[]) >>
       disch_then ACCEPT_TAC) >>
      fs[Abbr `cx`, Abbr `compiled_body`, Abbr `entry`, Abbr `explicit`] >>
      rpt conj_tac >> rpt gen_tac >> first_assum ACCEPT_TAC) >>
  rename1 `_ = (INL answer,es_lock)` >> Cases_on `answer` >>
  reverse (Cases_on `storage_trace_domain cx (initial_state am []) es_lock.storage_trace`)
  >- (`!tail. ~call_storage_ok am tx vs.vs_outcomes (prefix ++ tail)` by
        (mp_tac (Q.INST [`os` |-> `vs.vs_outcomes`] (SPEC_ALL runtime_bound_lock_outside_domain)) >>
         impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           fs[Abbr `cx`, Abbr `prefix`] >> Cases_on `nr` >> Cases_on `mut` >> gvs[]) >>
         disch_then ACCEPT_TAC) >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`shadow_unit`,`marks0`,`es_lock`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- fs[Abbr `cx`] >>
      conj_tac >- fs[Abbr `cx`] >>
      conj_tac >- fs[Abbr `prefix`] >>
      pure_rewrite_tac [source_unit_execution_correct_with_def] >>
      qexistsl_tac [`func`,`shadow_func`] >> simp[] >>
      disj1_tac >>
      qexistsl_tac [`storage_trace_horizon es0.storage_trace`,
        `func`,`[]`,`G0`,`tn0`,`s0`] >>
      irule (cj 1 gas_origin_ptr_focus_rules) >>
      `valid_horizon cx (initial_state am []) (storage_trace_horizon es0.storage_trace)
         es0.storage_trace` by fs[storage_trace_domain_def] >>
      fs[Abbr `cx`, Abbr `entry`, Abbr `explicit`] >>
      metis_tac[]) >>
  disj2_tac >> disj2_tac >> qmatch_abbrev_tac `prepared` >>
  runtime_bound_frame_tac >>
  qpat_assum `compile_guarded_body cenv nr _ T _ compiled_body _ sa = _`
    (fn code => mp_tac (MATCH_MP nonreentrantEntryPathTheory.guarded_body_intervals_from_registration
      (CONJ code (ASSUME ``fn_has_code sa st' func``)))) >>
  disch_then (qx_choosel_then [`sl`,`sb`] strip_assume_tac) >>
  `L sl sb` by
    (qpat_assum `!a b c d. _ ==> L b c` (qspecl_then [`sa`,`sl`,`sb`,`st'`] mp_tac) >>
     asm_simp_tac std_ss []) >>
  qpat_assum
    `compile_guarded_body _ nr _ T _ (MAP gas_shadow_stmt compiled_body) _ shadow_sa = _`
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
      (Q.INST [`func` |-> `shadow_func`]
        nonreentrantEntryPathTheory.guarded_body_code_from_registration))) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`shadow_sl`,`shadow_sb`] strip_assume_tac) >>
  `gas_shadow_compiles
     (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
      else comp_return ())
     (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
      else comp_return ())` by
    (Cases_on `nr` >> simp[gasShadowModuleOpsTheory.gas_shadow_compiles_nonreentrant_lock,
      gasShadowStateTheory.gas_shadow_compiles_return]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  asm_simp_tac std_ss [] >> strip_tac >>
  qspecl_then [`tops`,`bindings`,`unit.cu_context`,`cx`,`cenv`,`compiled_body`,
    `ret`,`if ret = NoneT then NONE else SOME ret`,`env_t`,`env'`,`sl`,`sb`]
    mp_tac guarded_body_stmts_env >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  disch_then (qx_choose_then `cenv'` assume_tac) >>
  `SND (stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body)
          shadow_sl) = shadow_sb` by
    (qpat_assum `compile_stmts _ NoLoop _ (MAP gas_shadow_stmt compiled_body) _ = _`
       (mp_tac o REWRITE_RULE [compile_stmts_env]) >>
     reverse (Cases_on `ret = NoneT`) >- simp[] >>
     gvs[] >> drule type_stmts_none_valued_return >> strip_tac >>
     qspecl_then [`MAP gas_shadow_stmt compiled_body`,`tops`,`bindings`,
       `gas_shadow_env T cenv`,`NoLoop`,`NoneT`,`BaseT BoolT`]
       mp_tac stmts_env_ret_ty_no_valued_return >>
     (impl_tac >- simp[gasShadowStmtEnvTheory.gas_shadow_supported_stmts,
       gasShadowStmtEnvTheory.gas_shadow_valued_return]) >>
     disch_then (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  qspecl_then [`compiled_body`,`cenv`,`NoLoop`,`ret`] mp_tac
    (Q.INST [`sd` |-> `T`] gasShadowStmtEnvTheory.gas_shadow_stmts_env_env) >>
  rewrite_tac[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def] >>
  disch_then (qspecl_then [`sl`,`shadow_sl`] mp_tac) >>
  asm_simp_tac std_ss [pairTheory.FST,pairTheory.SND] >> strip_tac >>
  `stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body)
     shadow_sl = (gas_shadow_env T cenv',shadow_sb)` by
    metis_tac[pairTheory.PAIR] >>
  qpat_x_assum `SND (stmts_env _ _ _ (MAP gas_shadow_stmt _) _) = _` kall_tac >>
  qpat_x_assum `_ = FST (stmts_env _ _ _ (MAP gas_shadow_stmt _) _)` kall_tac >>
  `?s_b G_b tn_b.
     gas_path_mem unit.cu_context func entry (LENGTH marks0) (OK s_b) /\
     alloca_history func s_b /\ return_buf_frame NONE cenv sl s_b /\
     local_ptrs_reserved cenv sl /\ ~block_is_terminated sl /\
     ~s_b.vs_halted /\ s_b.vs_current_bb = sl.cs_current_bb /\
     s_b.vs_inst_idx = LENGTH sl.cs_current_insts /\
     s_b.vs_gas_readings = s0.vs_gas_readings /\
     s_b.vs_code = vs.vs_code /\ s_b.vs_labels = vs.vs_labels /\
     (nr /\ mut <> View ==> ~tx.is_static) /\
     !H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
       stmt_state_rel H unit.cu_context func cenv cx es_lock s_b /\
       ghost_inv_at (cx_dead H cx) 0 NONE cenv cx es_lock G_b tn_b s_b /\
       gas_origin_ptr_path (cx_dead H cx,0,explicit,unit.cu_context,func,[])
         (entry,FEMPTY,entry_taint) marks0 (OK s_b,G_b,tn_b) /\
       ((!fuel. ptr_safe_run (cx_dead H cx) 0 fuel
                 unit.cu_context func [] G_b tn_b s_b) ==>
        !fuel. ptr_safe_blocks (cx_dead H cx) 0 fuel
          unit.cu_context func [] FEMPTY entry_taint entry)` by
    (reverse (Cases_on `nr`) >-
       (qpat_x_assum `lock_if_nr cx F _ es0 = _` mp_tac >>
        qpat_x_assum `(if F then _ else _) sa = _` mp_tac >>
        simp_tac (srw_ss()) [lock_if_nr_def, return_def, comp_return_def] >>
        ntac 2 (disch_then (SUBST_ALL_TAC o SYM)) >>
        qexistsl [`s0`,`G0`,`tn0`] >>
        asm_rewrite_tac[] >> qx_gen_tac `H` >> strip_tac >>
        qpat_assum `!st0 H. valid_horizon _ _ H _ ==> _`
          (qspecl_then [`initial_state am []`,`H`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> simp[]) >>
     qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
       (strip_assume_tac o REWRITE_RULE []) >>
     qpat_assum `T ==> fresh_vars_wrt sa s0 /\ _`
       (strip_assume_tac o REWRITE_RULE []) >>
     qpat_assum `(if T then _ else _) sa = _`
       (assume_tac o REWRITE_RULE []) >>
     mp_tac (Q.INST [`cx` |-> `cx`, `ss` |-> `entry`,
       `explicit` |-> `explicit`, `marks0` |-> `marks0`,
       `ctx` |-> `unit.cu_context`, `nkey` |-> `global_nonreentrant_slot`]
       (SPEC_ALL selected_entry_after_lock)) >>
     impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
     disch_then (qx_choosel_then [`s_b`,`G_b`,`tn_b`] strip_assume_tac) >>
     `mut <> View ==> ~tx.is_static` by
       fs[Abbr `cx`, initial_evaluation_context_def] >>
     qexistsl [`s_b`,`G_b`,`tn_b`] >>
     simp[] >> qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!st0 H. valid_horizon cx st0 H es_lock.storage_trace ==> _`
       (qspecl_then [`initial_state am []`,`H`] mp_tac) >>
     simp[ghost_inv_cx_dead]) >>
  `gas_path unit.cu_context func entry (LENGTH marks0) (OK s_b)` by
    (drule_then (ACCEPT_TAC o CONJUNCT1) fragGasPathMemTheory.gas_path_mem_exec) >>
  `!fn inst s. frag_reachable unit.cu_context func s_b fn inst s ==>
       dalloca_fmp_headroom inst s` by
    (mp_tac (Q.INST [`s0` |-> `s_b`, `n` |-> `LENGTH (marks0:bool list)`]
      (SPEC_ALL runtime_body_reached_dalloca_headroom)) >>
     impl_tac >- (fs[Abbr `entry`] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `expr_sim_inv cenv cx env_t es_lock` by
    (irule runtime_lock_expr_sim_inv >> goal_assum (drule_at Any) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env_t es_lock` by
    (`env_context_consistent env_t cx` by fs[expr_sim_inv_def, env_consistent_def] >>
     `es_lock.immutables = am.immutables` by
       (drule_all external_entry_bound_source_frame >> strip_tac >>
        drule_then strip_assume_tac external_body_lock_frame >> simp[]) >>
     qunabbrev_tac `cx` >>
     drule_all_then ACCEPT_TAC external_source_body_const_cells_checked) >>
  `!gas. eval_stmts cx compiled_body (es_lock with gas_obs := gas) =
          eval_stmts cx fbody (es_lock with gas_obs := gas)` by
    (mp_tac (Q.INST [`gs` |-> `prefix ++ es0.gas_obs`, `es0` |-> `es0`,
          `os` |-> `vs.vs_outcomes`, `unit` |-> `unit`, `rpolicy` |-> `rpolicy`,
          `es_lock` |-> `es_lock`, `nr` |-> `nr`, `mut` |-> `mut`,
          `ret` |-> `ret`, `fbody` |-> `fbody`, `tops` |-> `tops`,
          `args` |-> `args`, `dflts` |-> `dflts`, `am` |-> `am`, `tx` |-> `tx`]
       (SPEC_ALL external_source_body_substitution_nr)) >>
     disch_then (fn th =>
       qpat_assum `Abbrev (cx = _)` (fn eq =>
         qpat_assum `Abbrev (compiled_body = _)` (fn eq' =>
           mp_tac (PURE_REWRITE_RULE
             [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq),
              GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq')] th)))) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
     storage_well_formed_on cx es_lock (FST H)` by
    (gen_tac >> strip_tac >>
     `es_lock.storage_trace =
        es0.storage_trace ++ if nr then [StorageLock global_nonreentrant_slot] else []` by
       (reverse (Cases_on `nr`) >- fs[lock_if_nr_def, return_def] >>
        `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by fs[] >>
        irule lock_if_nr_success_trace >>
        qexistsl_tac [`cx`,`is_view_mut mut`] >> simp[]) >>
     `valid_horizon cx (initial_state am []) H es0.storage_trace` by
        fs[valid_horizon_def, storage_observations_ok_append] >>
     drule_all external_entry_bound_source_frame >> strip_tac >>
     mp_tac (Q.INST [`H` |-> `H`, `st` |-> `es0`, `u` |-> `es_lock`,
       `cx` |-> `cx`, `nr` |-> `nr`, `res` |-> `INL ()`, `view` |-> `is_view_mut mut`]
       vyperExternalEntryStorageFrameTheory.lock_if_nr_preserves_storage_well_formed_on) >>
     impl_tac
     >- (`storage_well_formed_on cx es0 (FST H)` by fs[Abbr `cx`] >>
         qpat_assum `valid_horizon cx _ H es_lock.storage_trace`
           (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  mp_tac (Q.SPECL
    [`\H. cx_dead H cx`,`0`,`NONE`,`shadow_unit.cu_context`,`[]`,`func`,`shadow_func`,
     `tops`,`rpolicy`,`unit`,`am`,`tx`,`ret`,`mut`,`nr`,`args`,`dflts`,`fbody`,
     `lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,`rt`,`cenv`]
    external_source_frame_ret_ok_full_nr) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th =>
    qpat_assum `Abbrev (cx = _)` (fn eq =>
      assume_tac (PURE_REWRITE_RULE
        [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)] th))) >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> fs[Abbr `cx`, source_deployment_rel_def,
      vyperContextTheory.get_module_code_def, initial_evaluation_context_def]) >>
  `~cenv.ce_is_ctor` by fs[bodySimTheory.body_inv_def, Abbr `cx`, initial_evaluation_context_def] >>
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule_all caller_runtime_entry_integrity >> simp[]) >>
  `struct_args_unique tops` by
    (fs[source_typing_ok_def] >> metis_tac[checked_contract_struct_args_unique]) >>
  runtime_shadow_body_inv_tac >>
  drule_all runtime_selected_body_loop_calls >> strip_tac >>
  qunabbrev_tac `prepared` >>
  qexistsl_tac [`cx`,`compiled_body`,`entry`,`explicit`,`prefix`,`marks0`,
    `shadow_unit`,`func`,`shadow_func`,`cenv`,`cenv'`,`bindings`,`env_t`,`env'`,
    `es_lock`,`sa`,`sl`,`sb`,`st'`,`shadow_sl`,`shadow_sb`,`s_b`,`G_b`,`tn_b`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  asm_simp_tac std_ss [markerTheory.Abbrev_def] >>
  fs[Abbr `compiled_body`]
QED

(* The true decoration preserves the original CREATE preparation interface. *)
local
  val unrestricted_prepare =
    Q.SPEC `\a b. T` runtime_body_endpoint_prepare_with_cases
    |> PURE_REWRITE_RULE [GSYM runtime_body_endpoint_unrestricted_def]
    |> CONV_RULE (DEPTH_CONV BETA_CONV)
    |> PURE_REWRITE_RULE [AND_CLAUSES, IMP_CLAUSES, FORALL_SIMP]
in
Theorem runtime_body_endpoint_prepare_create_cases:
  ^(concl unrestricted_prepare)
Proof
  ACCEPT_TAC unrestricted_prepare
QED
end

Theorem runtime_body_endpoint_prepare_cases:
  !tops rpolicy unit am tx ret vs mut nr args dflts fbody es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args dflts ret
      (subst_consts_stmts (module_consts_env tops []) fbody) ==>
    (?shadow_unit marks0 func sa st' cenv s0 G0 tn0 exc es_abort a t G tn.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      nr /\
      (initial_evaluation_context am.sources am.layouts tx NONE).nonreentrant_slot =
         SOME global_nonreentrant_slot /\
      is_view_mut mut = (mut = View) /\
      lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
        nr (is_view_mut mut) es0 = (INR exc,es_abort) /\
      compile_guarded_body cenv T global_nonreentrant_slot T (mut = View)
        (subst_consts_stmts (module_consts_env tops []) fbody)
        (if ret = NoneT then NONE else SOME ret) sa = ((),st') /\
      fn_has_code sa st' func /\
      s0.vs_gas_readings = DROP (LENGTH marks0) vs.vs_gas_readings /\
      (!H : (bool # bytes32 # type_value) list # num list.
         stmt_state_rel H unit.cu_context func cenv
           (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
         ghost_inv H NONE cenv
           (initial_evaluation_context am.sources am.layouts tx NONE) es0 G0 tn0 s0) /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      fn_entry_label func = SOME "__entry" /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      ~s0.vs_halted /\
      expr_exit (INR exc : unit + exception) (Abort a t) /\
      (exc = Error (RuntimeError "nonreentrant lock") \/
       exc = Error (RuntimeError "write in static context")) /\
      (!D. gas_origin_ptr_path
         (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
          unit.cu_context,func,[])
         (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>,FEMPTY,entry_taint)
         marks0 (OK s0,G0,tn0) /\
           gas_origin_ptr_path
         (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
          unit.cu_context,func,[])
         (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>,FEMPTY,entry_taint)
         marks0 (Abort a t,G,tn)) /\
      source_unit_execution_correct_with shadow_unit.cu_context marks0
        tops ret am tx unit vs /\
      (!tail. FST (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks0 vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading")))) \/
    (?shadow_unit marks0 es_lock.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
        nr (is_view_mut mut) es0 = (INL (),es_lock) /\
      ~storage_trace_domain (initial_evaluation_context am.sources am.layouts tx NONE)
        (initial_state am []) es_lock.storage_trace /\
      (!tail. ~call_storage_ok am tx vs.vs_outcomes
          (gas_explicit marks0 vs.vs_gas_readings ++ tail)) /\
      source_unit_execution_correct_with shadow_unit.cu_context marks0
        tops ret am tx unit vs) \/
    (?cx compiled_body entry explicit prefix marks0 shadow_unit func shadow_func
      cenv cenv' bindings env_t env' es_lock sa sl sb st' shadow_sl shadow_sb
      s_b G_b tn_b.
      cx = initial_evaluation_context am.sources am.layouts tx NONE /\
      compiled_body = subst_consts_stmts (module_consts_env tops []) fbody /\
      entry = (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                          vs_inst_idx := 0|>) /\
      explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context /\
      prefix = gas_explicit marks0 vs.vs_gas_readings /\
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      (!gx. external_entry_bound tops am tx vs.vs_outcomes (prefix ++ gx)
        mut args dflts (es0 with gas_obs := gx)) /\
      external_entry_bound tops am tx vs.vs_outcomes (prefix ++ es0.gas_obs)
        mut args dflts es0 /\
      lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
      (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
              is_view_mut mut = (mut = View)) /\
      global_nonreentrant_slot < dimword (:256) /\
      (nr /\ mut <> View ==> ~tx.is_static) /\
      (!gas. eval_stmts cx compiled_body (es_lock with gas_obs := gas) =
             eval_stmts cx fbody (es_lock with gas_obs := gas)) /\
      storage_trace_domain cx (initial_state am []) es_lock.storage_trace /\
      body_inv tops unit.cu_context cenv cx /\
      shadow_body_inv tops unit.cu_context shadow_unit.cu_context /\
      struct_args_unique tops /\
      supported_stmts tops bindings compiled_body /\
      (!vis mut nr raw fn args dflts ret stmts.
        MEM (FunctionDecl vis mut nr raw fn args dflts ret stmts) tops ==>
        stmts_loop_calls_ok [(NONE,tops)] stmts) /\
      stmts_loop_calls_ok [(NONE,tops)] compiled_body /\
      (!tgt. supported_stmts_expr_exists (expr_abi_decode_target_root tgt)
         compiled_body ==> occurs_abi_decode_target tgt tops) /\
      body_const_cells_agree [(NONE,tops)] cx env_t es_lock /\
      expr_sim_inv cenv cx env_t es_lock /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret compiled_body = SOME env' /\
      stmts_exprs_ok cenv compiled_body /\
      call_evaluation_safe cx (int_calls_stmts compiled_body) /\
      frame_ret_ok_full
        ((\H. cx_dead H cx),0,NONE,unit.cu_context,shadow_unit.cu_context,[],func,shadow_func)
        cx
        (\H v ee gt r. ?tv v' us.
           evaluate_type (type_env tops) ret = SOME tv /\
           safe_cast tv v = SOME v' /\
           unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
           external_call_result_rel H tops ret tx
             (INL v', finalize_pending_deletions
                (abstract_machine_from_state am.sources am.exports am.layouts us),
              us.requests) r)
        cenv ret /\
      compile_guarded_body cenv nr global_nonreentrant_slot T (mut = View)
        compiled_body (if ret = NoneT then NONE else SOME ret) sa = ((),st') /\
      (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
       else comp_return ()) sa = ((),sl) /\
      compile_stmts cenv NoLoop
        (case (if ret = NoneT then NONE else SOME ret) of
           NONE => BaseT BoolT | SOME ty => ty) compiled_body sl = ((),sb) /\
      stmts_env cenv NoLoop ret compiled_body sl = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body)
        shadow_sl = (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sl shadow_sl /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context unit.cu_context shadow_unit.cu_context /\
      ctx_inst_ids_distinct unit.cu_context /\ gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_unit.cu_context.ctx_functions /\
      fn_has_code sl sb func /\ fn_has_code shadow_sl shadow_sb shadow_func /\
      fn_has_code sb st' func /\ fn_inst_ids_distinct func /\
      cx_tops cx = tops /\ ~cenv.ce_is_ctor /\ cenv.ce_return_pc = NONE /\
      gas_path_mem unit.cu_context func entry (LENGTH marks0) (OK s_b) /\
      alloca_history func s_b /\ return_buf_frame NONE cenv sl s_b /\
      local_ptrs_reserved cenv sl /\ ~block_is_terminated sl /\
      ~s_b.vs_halted /\ s_b.vs_current_bb = sl.cs_current_bb /\
      s_b.vs_inst_idx = LENGTH sl.cs_current_insts /\
      s_b.vs_gas_readings = DROP (LENGTH marks0) vs.vs_gas_readings /\
      s_b.vs_code = vs.vs_code /\ s_b.vs_labels = vs.vs_labels /\
      (!fn inst s. frag_reachable unit.cu_context func s_b fn inst s ==>
        dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
        storage_well_formed_on cx es_lock (FST H)) /\
      !H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
        stmt_state_rel H unit.cu_context func cenv cx es_lock s_b /\
        ghost_inv_at (cx_dead H cx) 0 NONE cenv cx es_lock G_b tn_b s_b /\
        gas_origin_ptr_path (cx_dead H cx,0,explicit,unit.cu_context,func,[])
          (entry,FEMPTY,entry_taint) marks0 (OK s_b,G_b,tn_b) /\
        ((!fuel. ptr_safe_run (cx_dead H cx) 0 fuel
                  unit.cu_context func [] G_b tn_b s_b) ==>
         !fuel. ptr_safe_blocks (cx_dead H cx) 0 fuel
           unit.cu_context func [] FEMPTY entry_taint entry))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_body_endpoint_prepare_create_cases >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 assume_tac
      (qx_choosel_then [`cx`,`compiled_body`,`entry`,`explicit`,`prefix`,`marks0`,
        `shadow_unit`,`func`,`shadow_func`,`cenv`,`cenv'`,`bindings`,`env_t`,`env'`,
        `es_lock`,`sa`,`sl`,`sb`,`st'`,`shadow_sl`,`shadow_sb`,`s_b`,`G_b`,`tn_b`]
        (MAP_EVERY ASSUME_TAC o CONJUNCTS))))
  >- (disj1_tac >> first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`cx`,`compiled_body`,`entry`,`explicit`,`prefix`,`marks0`,
    `shadow_unit`,`func`,`shadow_func`,`cenv`,`cenv'`,`bindings`,`env_t`,`env'`,
    `es_lock`,`sa`,`sl`,`sb`,`st'`,`shadow_sl`,`shadow_sb`,`s_b`,`G_b`,`tn_b`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem runtime_body_endpoint_correct:
  !tops rpolicy unit am tx ret vs mut nr args dflts fbody es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args dflts ret
      (subst_consts_stmts (module_consts_env tops []) fbody) ==>
    ?shadow_unit marks.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail. call_storage_ok am tx vs.vs_outcomes
          (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail. FST (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
        INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_body_endpoint_prepare_cases >>
  disch_then (DISJ_CASES_THEN2
    (qx_choosel_then [`shadow_unit`,`marks0`,`func`,`sa`,`st'`,`cenv`,`s0`,
      `G0`,`tn0`,`exc`,`es_abort`,`a`,`t`,`G`,`tn`]
      (MAP_EVERY ASSUME_TAC o CONJUNCTS))
    (DISJ_CASES_THEN2 strip_assume_tac
      (qx_choosel_then [`cx`,`compiled_body`,`entry`,`explicit`,`prefix`,`marks0`,
        `shadow_unit`,`func`,`shadow_func`,`cenv`,`cenv'`,`bindings`,`env_t`,`env'`,
        `es_lock`,`sa`,`sl`,`sb`,`st'`,`shadow_sl`,`shadow_sb`,`s_b`,`G_b`,`tn_b`]
        (MAP_EVERY ASSUME_TAC o CONJUNCTS))))
  >- (qexistsl_tac [`shadow_unit`,`marks0`] >> simp[])
  >- (qexistsl_tac [`shadow_unit`,`marks0`] >> simp[] >> metis_tac[]) >>
  MAP_EVERY (fn pat => qpat_x_assum pat
    (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`_ = initial_evaluation_context am.sources am.layouts tx NONE`,
     `_ = subst_consts_stmts (module_consts_env tops []) fbody`,
     `_ = (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0|>)`,
     `_ = gas_explicit_sites unit.cu_context shadow_unit.cu_context`,
     `_ = gas_explicit marks0 vs.vs_gas_readings`] >>
  runtime_selected_body_frag_tac `nr` `dflts` `prefix ++ es0.gas_obs` `es_lock` >>
  disch_then (mp_tac o REWRITE_RULE [stmt_frag_full_def]) >>
  disch_then (qspecl_then [`initial_state am []`, `sl`, `sb`, `shadow_sl`,
                           `shadow_sb`, `s_b`, `G_b`, `tn_b`, `cenv'`] mp_tac) >>
  impl_tac
  >- (`cenv.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
      qpat_assum `!fn inst s. frag_reachable unit.cu_context func s_b fn inst s ==>
          dalloca_fmp_headroom inst s`
        (fn nowrap =>
          simp[dead_lo_ok_def, ret_pc_ok_def, return_buf_sep_def, gas_admissible_def, nowrap]) >>
      rpt strip_tac >> asm_simp_tac std_ss []
      >~ [`stmt_res_ok`] >- metis_tac[external_body_source_ok_nr]
      >~ [`allocas_below_fmp`]
      >- (qpat_assum `storage_trace_domain cx (initial_state am []) es_lock.storage_trace`
            (strip_assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
          qpat_assum `!H. valid_horizon cx _ H es_lock.storage_trace ==> _ /\ _`
            (qspec_then `storage_trace_horizon es_lock.storage_trace` mp_tac) >>
          impl_tac >- runtime_entry_horizon_simp >>
          disch_then (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp
                             o CONJUNCT1) >> simp[])
      >- (qpat_assum `!fn inst s. frag_reachable unit.cu_context func s_b fn inst s ==>
             dalloca_fmp_headroom inst s`
            (fn nowrap => first_assum (ACCEPT_TAC o MATCH_MP nowrap)))
      >> qpat_assum `!H. valid_horizon _ _ H es_lock.storage_trace ==> _`
           drule >> simp[]) >>
  qpat_assum `cx_tops _ = tops` (fn th => REWRITE_TAC [th]) >>
  strip_tac >>
  runtime_body_compose_from_tac
    (Q.ISPEC `\(cr : value + exception).
       cr <> INR (Error (RuntimeError "msg.gas: no gas reading"))`
       unit_execution_compose_result_horizon)
    `\g. call_external_trace (SOME vs.vs_outcomes) (prefix ++ g) am tx` `marks0` >>
  impl_tac
  >- (rpt conj_tac
      >- simp[evaluate_storage_trace_frame]
      >- fs[Abbr `cx`]
      >- (rpt strip_tac >> BETA_TAC >>
          qpat_assum `!H. valid_horizon cx _ H es_lock.storage_trace ==> _`
            (qspec_then `H` mp_tac) >>
          fs[Abbr `cx`, Abbr `entry`, Abbr `explicit`])
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _`
            (qspec_then `gobs` (fn eq =>
              qpat_assum `eval_stmts _ compiled_body _ = (res,ee)`
                (assume_tac o REWRITE_RULE [eq]))) >>
          runtime_bound_unlock_tac `ret` `gobs` `res` `ee: evaluation_state` >>
          qpat_assum `call_external_trace _ (prefix ++ gobs) _ _ = (_,_,_,obs)`
            (fn trace => PURE_REWRITE_TAC [trace,pairTheory.SND]) >>
          Cases_on `res = INL () \/ (?v. res = INR (ReturnException v))`
          >- (qpat_assum `_ ==> obs = eu.storage_trace` (fn trace =>
                first_assum (SUBST1_TAC o MATCH_MP trace)) >>
              reverse (Cases_on `nr`)
              >- fs[unlock_if_nr_def,return_def] >>
              `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by fs[] >>
              mp_tac (Q.INST [`cx` |-> `cx`, `key` |-> `global_nonreentrant_slot`,
                `iv` |-> `is_view_mut mut`, `es0` |-> `es0`, `es_lock` |-> `es_lock`,
                `fbody` |-> `fbody`, `gs` |-> `gobs`, `res` |-> `res`, `ee` |-> `ee`,
                `eu` |-> `eu`, `st` |-> `initial_state am []`]
                  (SPEC_ALL selected_unlock_trace_horizons)) >>
              impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
              disch_then ACCEPT_TAC) >>
          qpat_assum `_ ==> obs = ee.storage_trace` (fn trace =>
            first_assum (SUBST1_TAC o MATCH_MP trace)) >> simp[])
      >- (rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
          runtime_locked_eval_tac >>
          qspecl_then [`tops`,`am`,`tx`,`ret`,`mut`,`nr`,`args`,`dflts`,`fbody`,
                       `vs.vs_outcomes`,`prefix`,`gx ++ tail`,`gx`,`es0`,
                       `es_lock`,`res`,`ee`,`tail`,`[]`] mp_tac
            selected_call_trace_gas_cong_nr >>
          disch_then (fn th =>
            qpat_assum `Abbrev (cx = _)` (fn eq =>
              mp_tac (PURE_REWRITE_RULE
                [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)] th))) >>
          impl_tac
          >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
              >- (strip_tac >> fs[]) >>
              qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _`
                (qspec_then `gx ++ tail` (fn eq => PURE_REWRITE_TAC [GSYM eq])) >>
              qpat_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
                (qspec_then `tail` ACCEPT_TAC)) >>
          simp[APPEND_ASSOC])
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          qabbrev_tac `res = (INR (Error err) : unit + exception)` >>
          `eval_stmts cx fbody (es_lock with gas_obs := gx) =
           (res, ee with gas_obs := [])` by
            (qpat_assum `!tail. eval_stmts _ compiled_body _ = (_,ee with gas_obs := tail)`
               (qspec_then `[]` (fn eval =>
                 qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _`
                   (qspec_then `gx` (fn eq => mp_tac
                     (PURE_REWRITE_RULE [eq] (REWRITE_RULE [APPEND_NIL] eval)))))) >>
             simp[Abbr `res`]) >>
          runtime_bound_unlock_tac `ret` `gx` `res` `ee with gas_obs := []` >>
          gvs[Abbr `res`, source_exempt_def])
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          `res = INL () /\ ~block_is_terminated sb /\ ~t.vs_halted /\
           t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts` by
            gvs[stmt_lands_def] >>
          runtime_locked_eval_tac >>
          `ret = NoneT` by simp[] >>
          qpat_x_assum `cx_tops _ = tops` kall_tac >>
          rpt BasicProvers.VAR_EQ_TAC >>
          mp_tac (Q.INST [`nr` |-> `nr`, `nkey` |-> `global_nonreentrant_slot`,
                          `iv` |-> `mut = View`, `stmts` |-> `compiled_body`, `st` |-> `sa`,
                          `sl` |-> `sl`, `se` |-> `sb`, `sb` |-> `st'`, `cenv` |-> `cenv`]
            nonreentrantExitTheory.compile_guarded_body_stop_unlock_parts) >>
          impl_tac >- fs[] >>
          disch_then (qx_choose_then `su` strip_assume_tac) >>
          `fn_has_code sb su func /\ fn_has_code su st' func` by
            metis_tac[fn_has_code_split] >>
          `allocas_from 0 t` by simp[ptrDisciplineTheory.allocas_from_def] >>
          qexists_tac `Halt (halt_state ((if nr /\ mut <> View then
            tstore (n2w global_nonreentrant_slot) 0w t else t)
            with <|vs_inst_idx := LENGTH su.cs_current_insts;
                   vs_returndata := []|>))` >>
          simp[exit_result_def] >>
          qx_genl_tac [`H1`, `G1`, `tn1`] >> strip_tac >>
          `nr /\ mut <> View ==> ~t.vs_call_ctx.cc_static` by
            fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
               loweringStateRelDefsTheory.call_ctx_rel_def,
               Abbr `cx`, initial_evaluation_context_def] >>
          (* The halt state of this fixed instruction suffix precedes H and ghosts. *)
          mp_tac (Q.INST [`nr` |-> `nr`, `iv` |-> `mut = View`,
               `nkey` |-> `global_nonreentrant_slot`, `st` |-> `sb`,
               `sb` |-> `st'`, `s` |-> `t`, `ctx` |-> `unit.cu_context`,
               `tn` |-> `tn1`, `lo` |-> `0`, `G` |-> `G1`,
               `PG` |-> `[]`, `DF` |-> `\H. cx_dead H cx`,
               `cenv` |-> `cenv'`, `cx` |-> `cx`]
               (INST_TYPE [alpha |-> ``:256``]
               nonreentrantExitTheory.optional_transient_unlock_stop_joint_at)) >>
          impl_tac >- simp[] >>
          disch_then (qx_choosel_then [`ss`,`tn'`] strip_assume_tac) >>
          qexistsl_tac [`G1`,`tn'`] >>
          conj_tac
          >- (`~cenv'.ce_is_ctor` by
                (qpat_assum `cenv_top_ext cenv cenv' _`
                   (mp_tac o MATCH_MP stmtFragPtrTheory.cenv_top_ext_is_ctor) >> simp[]) >>
              qpat_assum `ghost_inv_at _ 0 NONE cenv' _ _ G1 tn1 t`
                (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
              qpat_assum `!H explicit. _ ==> gas_origin_ptr_path _ _ [] (Halt ss,_,_)`
                (qspecl_then [`H1`,`explicit`] mp_tac) >>
              BETA_TAC >> impl_tac >- simp[dead_lo_ok_def] >>
              disch_then (fn path =>
                qpat_assum `ss = _` (fn eq =>
                  ACCEPT_TAC (SIMP_RULE bool_ss [eq] path)))) >>
          qpat_assum `ss = _` (fn eq =>
            PURE_REWRITE_TAC [GSYM (SIMP_RULE bool_ss [] eq)]) >>
          rpt strip_tac >>
          runtime_bound_unlock_tac `NoneT` `gx` `(INL () : unit + exception)` `ee with gas_obs := []` >>
          `unlock_if_nr cx nr (is_view_mut mut) =
           if nr /\ mut <> View then release_nonreentrant_lock cx.txn.target global_nonreentrant_slot
           else vyperState$return ()` by
            (Cases_on `nr`
             >- (qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
                   (strip_assume_tac o SIMP_RULE bool_ss []) >>
                 asm_simp_tac bool_ss [unlock_if_nr_def, optionTheory.option_case_def]) >>
             simp_tac bool_ss [unlock_if_nr_def]) >>
          `~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by
            metis_tac[source_typing_none_return_plain] >>
          qspecl_then [`H1`,`func`,`cenv'`,`cx`,
            `ee with gas_obs := []`,`eu`,`t`,`ss`,`nr`,`global_nonreentrant_slot`,
            `mut = View`,`tops`,`tx`,`am.sources`,`am.exports`,`am.layouts`] mp_tac
              external_halt_success_unlock >>
          impl_tac
          >- (conj_tac >- fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_gas_obs] >>
              `cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn = tx` by
                simp[Abbr `cx`,initial_evaluation_context_def] >>
              asm_simp_tac bool_ss [] >>
              qpat_assum `unlock_if_nr cx nr (is_view_mut mut) = _` (fn unlock =>
                qpat_assum `unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = _`
                  (mp_tac o PURE_REWRITE_RULE [unlock])) >>
              asm_rewrite_tac[]) >>
          strip_tac >>
          gvs[external_call_result_rel_def, tx_return_bytes_def, return_bytes_def,
              abstract_machine_from_state_def, finalize_pending_deletions_def])
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          runtime_locked_eval_tac >>
          runtime_bound_unlock_tac `ret` `gx` `res` `ee with gas_obs := []` >>
          qpat_x_assum `!tail. stmt_exit_ptr _ _ _ _ _`
            (qspec_then `[]` mp_tac) >>
          simp[stmt_exit_ptr_def] >> strip_tac
          >- (runtime_compose_abort_halt_cases_tac >>
              qpat_x_assum `expr_exit _ _` mp_tac >>
              simp_tac (srw_ss()) [expr_exit_def] >>
              simp[external_call_result_rel_def] >>
              rpt strip_tac >> gvs[] >>
              runtime_compose_halt_tac >>
              simp[Abbr `cx`, initial_evaluation_context_def,
                abstract_machine_from_state_def]) >>
          `(abstract_machine_from_state am.sources am.exports am.layouts
               (eu with scopes := [])) =
             abstract_machine_from_state am.sources am.exports am.layouts eu` by
            simp[abstract_machine_from_state_def] >>
          qpat_assum `unlock_if_nr _ nr _ (ee with gas_obs := []) = (INL (),eu)`
            (mp_tac o MATCH_MP (Q.INST [`sc` |-> `[]`] unlock_if_nr_with_scopes)) >>
          simp[] >> strip_tac >> gvs[])
      >> ((* The selected source call forwards a missing-reading error only from
             the body, which has consumed exactly the marked readings. *)
          qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
          rpt gen_tac >> BETA_TAC >> strip_tac >> CCONTR_TAC >>
          qpat_x_assum `~(?tail. _)`
            (assume_tac o SIMP_RULE bool_ss [NOT_EXISTS_THM]) >>
          `res <> INR (Error (RuntimeError "msg.gas: no gas reading"))` by
            (disch_tac >>
             qpat_x_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
               (qspec_then `[0w:bytes32]` mp_tac) >>
             asm_rewrite_tac[] >>
             disch_then (mp_tac o MATCH_MP eval_stmts_missing_gas_reading_empty) >>
             simp[]) >>
          `eval_stmts cx
             fbody (es_lock with gas_obs := gx) = (res, ee with gas_obs := [])` by
            (qpat_x_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
               (qspec_then `[]` mp_tac) >>
             qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _` (fn th => simp[th])) >>
          runtime_bound_unlock_tac `ret` `gx` `res` `ee with gas_obs := []` >>
          `r = INR (Error (RuntimeError "msg.gas: no gas reading"))` by
            (qpat_assum `call_external_trace _ (prefix ++ gx) _ _ = (INR _,_,_,_)` (fn trace =>
               qpat_assum `call_external_trace _ (prefix ++ gx) _ _ = (r,_,_,_)`
                 (mp_tac o REWRITE_RULE [trace])) >> simp[]) >>
          (* Only the source result laws matter for this case split. *)
          MAP_EVERY (fn pat => qpat_assum pat mp_tac)
            [`res <> INR (Error (RuntimeError "msg.gas: no gas reading"))`,
             `r = INR (Error (RuntimeError "msg.gas: no gas reading"))`,
             `res = INL () ==> r = _ /\ _`,
             `!v. res = INR (ReturnException v) ==> _`,
             `res = INR HaltException ==> r = _ /\ _`,
             `!e. res = INR e /\ _ ==> r = _ /\ _`] >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          namedCases_on `res` ["u", "e"]
          >- (Cases_on `u` >> simp[]) >>
          Cases_on `e` >> simp[AllCaseEqs()] >> strip_tac >> gvs[])) >>
  disch_then (qx_choose_then `body_marks` ASSUME_TAC) >>
  `!tail. prefix ++ gas_explicit body_marks s_b.vs_gas_readings ++ tail =
          gas_explicit (marks0 ++ body_marks) vs.vs_gas_readings ++ tail` by
    simp[Abbr `prefix`, gas_explicit_append, APPEND_ASSOC] >>
  qexistsl_tac [`shadow_unit`,`marks0 ++ body_marks`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[call_external_trace_observations, Abbr `entry`, Abbr `explicit`, Abbr `cx`] >>
  qpat_assum `!tail. _ = gas_explicit (marks0 ++ body_marks) _ ++ tail`
    (fn th => PURE_REWRITE_TAC [th]) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choosel_then [`cr`,`am'`,`rqs`,`obs`]
      (MAP_EVERY ASSUME_TAC o CONJUNCTS)))
  >- (`!tail. ~call_storage_ok am tx vs.vs_outcomes
           (gas_explicit (marks0 ++ body_marks) vs.vs_gas_readings ++ tail)` by
        (gen_tac >> strip_tac >>
         drule source_storage_guards_domain >> simp[]) >>
      conj_tac
      >- (pure_rewrite_tac[source_unit_execution_correct_with_def] >>
          qexistsl_tac [`func`,`shadow_func`] >> simp[] >> metis_tac[]) >>
      simp[]) >>
  conj_tac
  >- (pure_rewrite_tac[source_unit_execution_correct_with_def] >>
      qexistsl_tac [`func`,`shadow_func`] >> simp[] >>
      disj2_tac >> qexistsl_tac [`cr`,`am'`,`rqs`,`obs`] >> simp[]) >>
  disch_tac >> qx_gen_tac `unread` >>
  qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `unread` (strip_assume_tac o MATCH_MP call_external_trace_result)) >>
  simp[]
QED

Theorem runtime_body_grouped_default_readings:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    EXISTS external_has_defaults (FST (classify_functions tops)) ==>
    ?shadow_unit.
      gas_shadow_unit unit shadow_unit /\
      !am tx ret vs.
        source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
        initial_venom_state_rel tops am tx vs /\
        outcomes_accounts_typed (SOME vs.vs_outcomes) /\
        (ctx_has_dalloca unit.cu_context ==>
          unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
          w2n vs.vs_initial_fmp < 2 ** 254) /\
        (ctx_has_dalloca unit.cu_context ==>
          !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
            dalloca_fmp_headroom inst s) /\
        (valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret \/
         (calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
            SOME (tx.function_name,tx.args) /\
          ?mut nr args dflts fbody.
            lookup_function NONE tx.function_name External tops =
              SOME (mut,nr,args,dflts,ret,fbody))) ==>
        ?marks.
          source_unit_execution_correct_with shadow_unit.cu_context marks
            tops ret am tx unit vs /\
          ((?tail. call_storage_ok am tx vs.vs_outcomes
             (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
           !tail. FST (call_external (SOME vs.vs_outcomes)
             (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
             INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  `?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      gas_shadow_unit unit shadow_unit` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     drule_all runtime_gas_shadow_unit_exists >> simp[]) >>
  qexists_tac `shadow_unit` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >>
  let
    fun route th =
      drule_all th >>
      disch_then (DISJ_CASES_THEN2 strip_assume_tac ACCEPT_TAC) >>
      drule_all runtime_body_endpoint_correct >>
      disch_then (qx_choosel_then [`su`,`marks`] (map_every assume_tac o CONJUNCTS)) >>
      `su = shadow_unit` by metis_tac[optionTheory.SOME_11] >>
      qexists_tac `marks` >> fs[]
  in
    strip_tac
    >- (qpat_assum `valid_vyper_call _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [e2eDefsTheory.valid_vyper_call_def]) >>
        route grouped_canonical_call_route) >>
    drule default_dispatch_raw_cases >>
    disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) strip_assume_tac)
    >- route grouped_fallback_call_route >>
    Cases_on `dflts = []`
    >- (qpat_x_assum `dflts = []` SUBST_ALL_TAC >> route grouped_legacy_call_route) >>
    route grouped_default_call_route
  end
QED

Theorem runtime_body_joint_from_start_with_readings:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody) ==>
    ?shadow_unit marks.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all runtime_entry_endpoint_body_endpoint >> strip_tac >>
  qspecl_then [`tops`,`rpolicy`,`unit`,`am`,`tx`,`ret`,`vs`,`mut`,
    `F`,`args`,`[]`,`fbody`,`es0`] mp_tac runtime_body_endpoint_correct >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem runtime_body_joint_from_start_with_shadow:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody) ==>
    ?shadow_unit marks.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs
Proof
  metis_tac[runtime_body_joint_from_start_with_readings]
QED

Theorem runtime_body_joint_from_start:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret
      (subst_consts_stmts (module_consts_env tops []) fbody) ==>
    ?shadow_ctx func shadow_func marks.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      (((!tail.
           ~(call_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail))) /\
        ?(H : (bool # bytes32 # type_value) list # num list)
           leaf leaf_pg leaf_g leaf_tn finish.
          gas_origin_ptr_focus
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0, gas_explicit_sites unit.cu_context shadow_ctx,
             unit.cu_context, func, [])
            ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>), FEMPTY, entry_taint)
            marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
       ?res am' rqs obs.
         (!tail. call_external_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
            (res, am', rqs, obs)) /\
         ((source_exempt tops (res, am', rqs) /\
           ?(H : (bool # bytes32 # type_value) list # num list)
              leaf leaf_pg leaf_g leaf_tn finish.
             gas_origin_ptr_focus
               (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
                0, gas_explicit_sites unit.cu_context shadow_ctx,
                unit.cu_context, func, [])
               ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0 |>), FEMPTY, entry_taint)
               marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
          (?r. exit_result r /\
             storage_trace_domain
               (initial_evaluation_context am.sources am.layouts tx NONE)
               (initial_state am []) obs /\
             gas_origin_path T
               (gas_explicit_sites unit.cu_context shadow_ctx)
               unit.cu_context func
               (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                           vs_inst_idx := 0 |>) marks r /\
             !H. valid_horizon
                   (initial_evaluation_context am.sources am.layouts tx NONE)
                   (initial_state am []) H obs ==>
               external_call_result_rel H tops ret tx (res, am', rqs) r /\
               (!fuel. ptr_safe_blocks
                 (cx_dead H
                   (initial_evaluation_context am.sources am.layouts tx NONE))
                 0 fuel unit.cu_context func [] FEMPTY entry_taint
                 (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                             vs_inst_idx := 0 |>)))))
Proof
  rpt strip_tac >>
  drule_all runtime_body_joint_from_start_with_shadow >>
  disch_then (qx_choosel_then [`shadow_unit`, `marks`] strip_assume_tac) >>
  qpat_x_assum `source_unit_execution_correct_with _ _ _ _ _ _ _ _`
    (qx_choosel_then [`func`, `shadow_func`]
       (MAP_EVERY ASSUME_TAC o CONJUNCTS) o
     REWRITE_RULE [source_unit_execution_correct_with_def]) >>
  qexistsl_tac [`shadow_unit.cu_context`, `func`, `shadow_func`, `marks`] >>
  simp[]
QED

(* S1 when the value moves and the body starts, for the canonical
   encoding: the canonical entry reaches the endpoint. *)
Theorem lower_vyper_runtime_unit_body_joint_with_shadow:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?shadow_unit marks.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs
Proof
  rpt strip_tac >>
  drule_all external_entry_joint_endpoint >> strip_tac >>
  drule_all runtime_body_joint_from_start_with_shadow >> disch_then ACCEPT_TAC
QED

Theorem lower_vyper_runtime_unit_body_joint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?shadow_ctx func shadow_func marks.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      (((!tail.
           ~(call_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail))) /\
        ?(H : (bool # bytes32 # type_value) list # num list)
           leaf leaf_pg leaf_g leaf_tn finish.
          gas_origin_ptr_focus
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0, gas_explicit_sites unit.cu_context shadow_ctx,
             unit.cu_context, func, [])
            ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>), FEMPTY, entry_taint)
            marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
       ?res am' rqs obs.
         (!tail. call_external_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
            (res, am', rqs, obs)) /\
         ((source_exempt tops (res, am', rqs) /\
           ?(H : (bool # bytes32 # type_value) list # num list)
              leaf leaf_pg leaf_g leaf_tn finish.
             gas_origin_ptr_focus
               (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
                0, gas_explicit_sites unit.cu_context shadow_ctx,
                unit.cu_context, func, [])
               ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0 |>), FEMPTY, entry_taint)
               marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
          (?r. exit_result r /\
             storage_trace_domain
               (initial_evaluation_context am.sources am.layouts tx NONE)
               (initial_state am []) obs /\
             gas_origin_path T
               (gas_explicit_sites unit.cu_context shadow_ctx)
               unit.cu_context func
               (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                           vs_inst_idx := 0 |>) marks r /\
             !H. valid_horizon
                   (initial_evaluation_context am.sources am.layouts tx NONE)
                   (initial_state am []) H obs ==>
               external_call_result_rel H tops ret tx (res, am', rqs) r /\
               (!fuel. ptr_safe_blocks
                 (cx_dead H
                   (initial_evaluation_context am.sources am.layouts tx NONE))
                 0 fuel unit.cu_context func [] FEMPTY entry_taint
                 (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                             vs_inst_idx := 0 |>)))))
Proof
  rpt strip_tac >>
  drule_all external_entry_joint_endpoint >> strip_tac >>
  drule_all runtime_body_joint_from_start >> disch_then ACCEPT_TAC
QED

val selected_entry_split_tac =
  `?mut args fbody.
     lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody) /\
     IS_SOME (bind_arguments (type_env tops) args tx.args)` by
    (fs[valid_vyper_call_def] >> metis_tac[]) >>
  `?env. bind_arguments (type_env tops) args tx.args = SOME env` by
    (Cases_on `bind_arguments (type_env tops) args tx.args` >> fs[]) >>
  Cases_on `send_call_value mut
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am [env] with
                 <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sres, es0)` >> Cases_on `sres`;

fun runtime_alternate_readings_tac th =
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac th >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `shadow_unit` strip_assume_tac) >>
  first_x_assum (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks` >> metis_tac[source_unit_execution_correct_at_def];

Theorem lower_vyper_runtime_unit_correct_readings_available:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) ==>
    ?marks.
      source_unit_execution_correct_at marks tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  rpt strip_tac >>
  Cases_on `EXISTS external_has_defaults (FST (classify_functions tops))`
  >- runtime_alternate_readings_tac runtime_body_grouped_default_readings >>
  selected_entry_split_tac
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all external_entry_joint_endpoint >> strip_tac >>
      drule_all runtime_body_joint_from_start_with_readings >>
      disch_then (qx_choosel_then [`shadow_unit`,`marks`] strip_assume_tac) >>
      qexists_tac `marks` >>
      metis_tac[source_unit_execution_correct_at_def]) >>
  drule_all external_entry_value_revert >>
  rewrite_tac[source_unit_execution_correct_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >>
  qexists_tac `marks` >> simp[] >>
  `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
  drule_all external_entry_reject_readings >> simp[]
QED

Theorem lower_vyper_runtime_unit_correct:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (ctx_has_dalloca unit.cu_context ==>
      unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254) /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >>
  drule_all lower_vyper_runtime_unit_correct_readings_available >>
  metis_tac[source_unit_execution_correct_def]
QED

(* S1b, sufficient gas.  The lowered run ends within a fuel that does not
   depend on the entry state, in particular not on the external-call
   outcomes.  Every function of the unit is fuel-stable once its callees
   are (fragFuelUnit), so from some fuel G on every run of the unit gives
   the same result, and a run that ends at any fuel ends at G.  S1 says the
   run ends at some fuel: the storage guards rule out its bad-storage arm,
   the non-exemption premise its exempt arm, and its path arm ends in an
   exit. *)
Theorem lower_vyper_runtime_unit_run_bounded:
  !tops rpolicy unit am tx ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx
    ==>
    ?fuel. !vs.
      valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
      initial_venom_state_rel tops am tx vs /\
      (ctx_has_dalloca unit.cu_context ==>
        unit_alloca_budget unit.cu_context <= w2n vs.vs_initial_fmp /\
        w2n vs.vs_initial_fmp < 2 ** 254) /\
      outcomes_accounts_typed (SOME vs.vs_outcomes) /\
      (ctx_has_dalloca unit.cu_context ==>
        !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
          dalloca_fmp_headroom inst s) /\
      (!marks.
         call_storage_ok am tx vs.vs_outcomes
           (gas_explicit marks vs.vs_gas_readings)) /\
      (!marks. ~source_exempt tops
         (call_external (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings) am tx))
      ==>
      terminates (run_context fuel unit.cu_context vs)
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac
    lower_vyper_runtime_unit_fns_stable >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_context_terminates_uniform >> strip_tac >>
  qexists_tac `G` >> rpt strip_tac >> first_x_assum irule >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `ret`, `vs`] mp_tac
    lower_vyper_runtime_unit_correct >>
  impl_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
  simp[source_unit_execution_correct_def,
       source_unit_execution_correct_at_def,
       source_unit_execution_correct_with_def] >>
  strip_tac
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> simp[])
  >- (qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      drule call_external_trace_result >> strip_tac >>
      qpat_x_assum `!marks. ~source_exempt _ _` (qspec_then `marks` mp_tac) >>
      simp[]) >>
  drule_all gas_origin_path_events >> strip_tac >>
  qpat_x_assum `lookup_block _ func.fn_blocks = SOME bb`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[lower_vyper_runtime_unit_block_phi] >>
  qexists_tac `SUC fuel` >>
  qspecl_then [`SUC fuel`, `unit.cu_context`, `vs`, `"__entry"`, `fn`,
               `"__entry"`] mp_tac run_context_run_blocks >>
  impl_tac >- simp[] >> disch_then SUBST1_TAC >>
  qspecl_then [`fuel`, `unit.cu_context`, `fn`,
               `vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                           vs_inst_idx := 0 |>`, `bb`] mp_tac
    run_blocks_run_from_no_phi >>
  impl_tac >- simp[] >> simp[] >> disch_then kall_tac >>
  Cases_on `r` >> gvs[exit_result_def, terminates_def]
QED

Theorem gas_marked_eval_stmts_readings_available:
  !memory ctx func cx body st vs marks res st' rv.
    gas_marked_exec memory (ctx,func) (eval_stmts cx body)
      (st,vs) marks res st' rv ==>
    res <> INR (Error (RuntimeError "msg.gas: no gas reading"))
Proof
  rpt gen_tac >>
  simp_tac std_ss [gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
  disch_tac >>
  qpat_x_assum `!tail. eval_stmts _ _ _ = _`
    (qspec_then `[0w:bytes32]` mp_tac) >>
  asm_rewrite_tac[] >>
  disch_then (mp_tac o MATCH_MP eval_stmts_missing_gas_reading_empty) >>
  simp[]
QED

Theorem call_external_marked_readings_available:
  !os prefix am tx src.
    (!tail. call_external (SOME os) (prefix ++ tail) am tx = src) /\
    (?tail.
      FST (call_external (SOME os) (prefix ++ tail) am tx) <>
      INR (Error (RuntimeError "msg.gas: no gas reading"))) ==>
    !tail.
      FST (call_external (SOME os) (prefix ++ tail) am tx) <>
      INR (Error (RuntimeError "msg.gas: no gas reading"))
Proof
  metis_tac[]
QED
