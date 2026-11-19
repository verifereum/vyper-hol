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
  runtimeEntryEndpoint runtimeBodyStartDefs
  runtimeFallbackSourceAlignment runtimeFallbackPackageEnvironment
  externalBodyFrame externalFrameRetOk runtimeBodyShadow externalBodySupport
  constSubst constSubstStmtsPreserve
  externalCallSelected externalBodySourceOk bodySimFullMain bodySimFull
  entryStateRel entryReachBodyFmp entryReachBodyRuntimeResources
  bodyAbiDecodeTarget rawReturnHeader loweringHalt gasContext bodyPtrDefs
  gasOutcomeFull fragGasOriginPtr loweringPosts stmtSimDefs exprSimDefs
  exprLoweringProps vyperStorageTrace vyperStorageBackend vyperCall
  fragExec moduleLowering fragGasOrigin fragFuelUnit passSimulationDefs
  acceptedContextPhi vyperLoweringCorrect typedCopyProducer
  vyperEvalReadingErrors unitExecutionComposeResult

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
Theorem selected_call_trace_gas_cong[local]:
  !tops am tx ret mut args fbody env os es0 g1 g2 res ee o1 o2.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME os; requests := [] |>) = (INL (), es0) /\
    stmt_res_ok NoLoop res /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es0 with gas_obs := g1) = (res, ee with gas_obs := o1) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es0 with gas_obs := g2) = (res, ee with gas_obs := o2) ==>
    call_external_trace (SOME os) g1 am tx =
    call_external_trace (SOME os) g2 am tx
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
  gvs[abstract_machine_from_state_def] >> BasicProvers.every_case_tac >> gvs[]
QED

(* The call's fourth component is its storage observations. *)
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

(* ===== The body's start ===== *)

(* Moving the call value leaves storage alone. *)
Theorem send_call_value_storage[local]:
  !mut cx st st' b.
    send_call_value mut cx st = (INL (), st') ==>
    get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >> drule send_call_value_accounts >> strip_tac >>
  Cases_on `b` >>
  rw[get_storage_def, accounts_after_transfer_def, LET_THM,
     vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
     combinTheory.APPLY_UPDATE_THM] >> gvs[]
QED

(* So the body starts on the initial storage. *)
Theorem body_start_storage_well_formed[local]:
  send_call_value mut cx
    (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
    (INL (), es0) ==>
  (storage_well_formed_on cx es0 R <=>
   storage_well_formed_on cx (initial_state am []) R)
Proof
  strip_tac >> drule send_call_value_storage >> strip_tac >>
  `!b. get_storage cx
         (initial_state am [env] with <| outcomes := orc; requests := [] |>)
         b = get_storage cx (initial_state am []) b` by
    (Cases >> simp[get_storage_def, initial_state_def]) >>
  simp[storage_well_formed_on_def]
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
    ~ctx_has_dalloca ctx /\ ~t.vs_halted /\
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
        (gen_tac >> simp[ptrSafeRunTheory.ptr_safe_step_def,
                        ptrSafeRunTheory.ptr_inst_ok_def] >>
         gvs[ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
             ptrDisciplineTheory.allocas_from_def,
             contextCodegenRelTheory.source_memory_read_ranges_def,
             codegenRelTheory.source_memory_write_ranges_def,
             venomInstTheory.mk_inst_def,
             ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.store_taint_def,
             ptrDisciplineTheory.adopt_reset_def, ptrDisciplineTheory.imm_taint_def,
             ptrDisciplineTheory.ret_taint_def, venomStateTheory.halt_state_def,
             stor_taint_ok_def, cx_dead_def]) >>
      irule (cj 3 gas_origin_ptr_path_rules) >>
      simp[exit_result_def, gas_origin_ptr_edge_def, gas_origin_edge_def,
           fragGasPathPtrTheory.gas_path_ptr_edge_def]) >>
  simp[venomStateTheory.halt_state_def]
QED

(* That halt is the source's success without a return value. *)
Theorem external_stop_result_rel[local]:
  !H tops tx am func cenv ee t ss mut nr args dflts fbody.
    source_typing_ok tops am tx /\ supported_program tops /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, dflts, NoneT, fbody) /\
    state_rel H func cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) ee t /\
    ss.vs_returndata = [] /\ ss.vs_accounts = t.vs_accounts /\
    ss.vs_transient = t.vs_transient /\ ss.vs_logs = t.vs_logs /\
    ss.vs_requests = t.vs_requests /\
    ss.vs_pending_deletions = t.vs_pending_deletions ==>
    external_call_result_rel H tops NoneT tx
      (INL NoneV,
       finalize_pending_deletions
         (abstract_machine_from_state am.sources am.exports am.layouts ee),
       ee.requests) (Halt ss)
Proof
  rpt strip_tac >>
  drule_all source_typing_none_return_plain >> strip_tac >>
  qspecl_then [`H`, `func`, `cenv`,
               `initial_evaluation_context am.sources am.layouts tx NONE`,
               `ee`, `ee`, `t`, `ss`, `F`, `0`, `F`, `tops`, `tx`,
               `am.sources`, `am.exports`, `am.layouts`] mp_tac
    external_halt_success_unlock >>
  impl_tac
  >- simp[initial_evaluation_context_def, vyperStateTheory.return_def] >>
  strip_tac >>
  gvs[external_call_result_rel_def, tx_return_bytes_def, return_bytes_def,
      abstract_machine_from_state_def, finalize_pending_deletions_def]
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
      disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
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

val runtime_body_source_tac =
  drule_at_then (Pat `set_external_package_target _ _ = _`)
    drule_all external_source_body_frame >> strip_tac >>
  mp_tac (Q.INST [`os` |-> `vs.vs_outcomes`] external_source_body_substitution) >>
  impl_tac >- simp[] >> strip_tac >>
  runtime_compiled_body_abi_targets_tac >>
  `set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt)` by
    (once_rewrite_tac
       [SIMP_RULE std_ss [subst_consts_fn_def, subst_consts_expr_def]
          (Q.INST [`E` |-> `module_consts_env tops []`,
                   `defaults` |-> `[]:expr list`] external_package_subst_consts)] >>
     first_assum ACCEPT_TAC) >>
  qabbrev_tac `compiled_body = subst_consts_stmts (module_consts_env tops []) fbody`;

val runtime_body_shadow_tac =
  `rt = if ret = NoneT then NONE else SOME ret` by
    gvs[package_external_fn_def, set_external_package_target_def] >>
  drule guarded_body_code >> strip_tac >>
  drule_all guarded_body_stmts_env >> strip_tac >>
  drule_all runtime_entry_body_shadow_with_shadow >>
  disch_then (qx_choosel_then [`func2`, `shadow_ctx`, `shadow_func`,
                `cenv2`, `sb2`, `shadow_sa`, `shadow_sb`, `shadow_unit`] strip_assume_tac) >>
  `func2 = func /\ cenv2 = cenv' /\ sb2 = sb` by gvs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule_all external_source_frame_ret_ok_full >>
  disch_then (qspecl_then
    [`\H. cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)`,
     `0`, `NONE`, `shadow_unit.cu_context`, `[]`, `func`, `shadow_func`] assume_tac) >>
  `cx_tops (initial_evaluation_context am.sources am.layouts tx NONE) =
   tops` by
    (irule cx_tops_module >>
     gvs[source_deployment_rel_def, vyperContextTheory.get_module_code_def,
         initial_evaluation_context_def]) >>
  `~cenv.ce_is_ctor` by
    gvs[bodySimTheory.body_inv_def, initial_evaluation_context_def] >>
  `~ctx_has_dalloca unit.cu_context` by
    metis_tac[entry_runtime_no_dalloca] >>
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule_all caller_runtime_entry_integrity >> simp[]);

val runtime_shadow_body_inv_tac =
  qpat_assum `source_typing_ok tops am tx` (fn typing =>
    qpat_assum `supported_program tops` (fn supported =>
      qpat_assum `lower_vyper_runtime_unit tops rpolicy = SOME unit` (fn lowered =>
        qpat_assum `runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit`
          (fn shadow => assume_tac (MATCH_MP runtime_shadow_body_inv
            (LIST_CONJ [MATCH_MP source_typing_ok_vtype_keys_distinct typing,
                        supported, lowered, shadow]))))));

val runtime_body_outcome_tac =
  `struct_args_unique tops` by
    (fs[source_typing_ok_def] >> metis_tac[checked_contract_struct_args_unique]) >>
  runtime_shadow_body_inv_tac >>
  drule_at (Pat `frame_ret_ok_full _ _ _ _ _`) body_stmts_sim_full >>
  disch_then (qspecl_then [`tops`, `bindings`, `env_t`, `env'`, `NoLoop`,
                           `compiled_body`, `es0`] mp_tac) >>
  impl_tac
  >- (simp[] >> metis_tac[]) >>
  disch_then (mp_tac o REWRITE_RULE [stmt_frag_full_def]) >>
  disch_then (qspecl_then [`initial_state am []`, `sa`, `sb`, `shadow_sa`,
                           `shadow_sb`, `s0`, `G0`, `tn0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (`cenv.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
      simp[dead_lo_ok_def, ret_pc_ok_def, return_buf_sep_def, gas_admissible_def] >>
      rpt strip_tac
      >~ [`stmt_res_ok`] >- metis_tac[external_body_source_ok]
      >~ [`dalloca_no_wrap`]
      >- metis_tac[bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap]
      >~ [`storage_well_formed_on`]
      >- (drule (INST_TYPE [alpha |-> ``:256``] body_start_storage_well_formed) >>
          disch_tac >> fs[valid_horizon_def])
      >> qpat_x_assum `!st0 H. valid_horizon _ _ _ es0.storage_trace ==> _`
           drule >> simp[]) >>
  qpat_assum `cx_tops _ = tops` (fn th => REWRITE_TAC [th]) >>
  strip_tac;

(* Compose at the body's marks, optionally retaining a call-result fact. *)
fun runtime_body_compose_tac compose =
  drule_at_then (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    (Q.ISPECL_THEN
      [`vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0 |>`,
       `\g. call_external_trace (SOME vs.vs_outcomes) g am tx`,
       `\(H : (bool # bytes32 # type_value) list # num list) c r.
          external_call_result_rel H tops ret tx c r`,
       `source_exempt tops :
          ((value + exception) # abstract_machine # call_request list) -> bool`]
      mp_tac) compose;

val runtime_compose_prefix_tac =
  rpt conj_tac
  >- simp[evaluate_storage_trace_frame]
  >- ((* the body starts with no observations *)
      `es0.storage_trace = []` by
        (drule send_call_value_accounts >> simp[initial_state_def]) >>
      simp[storage_trace_domain_def, valid_horizon_def,
           storage_trace_horizon_def, storage_trace_regions_def,
           storage_trace_locks_def, regions_consistent_def,
           storage_locks_separated_def, storage_well_formed_on_def,
           storage_observations_ok_def, storage_roots_fit_def,
           storage_trace_backends_well_formed_def])
  >- ((* the entry *)
      rpt strip_tac >> BETA_TAC >>
      qpat_x_assum `!st0 H. valid_horizon _ _ _ es0.storage_trace ==> _`
        drule >> strip_tac >> fs[])
  >- ((* the observations are the body's *)
      rpt gen_tac >> BETA_TAC >> strip_tac >>
      qpat_x_assum `eval_stmts _ compiled_body _ = (_,_)`
        (fn run => qpat_assum `!gx. eval_stmts _ compiled_body _ = _`
           (fn th => assume_tac (REWRITE_RULE [th] run))) >>
      drule_all selected_call_trace_body >> strip_tac >> simp[])
  >- ((* the call does not depend on the unread readings *)
      rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `!tail. eval_stmts _ compiled_body _ = (_,_)`
        (fn run => qpat_assum `!gx. eval_stmts _ compiled_body _ = _`
           (fn th => assume_tac (REWRITE_RULE [th] run))) >>
      `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
         fbody (es0 with gas_obs := gx) = (res, ee with gas_obs := [])` by
        (qpat_assum `!tail. eval_stmts _ fbody _ = (_,_)`
           (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL]))) >>
      `stmt_res_ok NoLoop res` by
        (drule_all external_body_source_ok >> simp[]) >>
      qspecl_then [`tops`, `am`, `tx`, `ret`, `mut`, `args`, `fbody`,
                   `env`, `vs.vs_outcomes`, `es0`, `gx ++ tail`, `gx`,
                   `res`, `ee`, `tail`, `[]`] mp_tac
        selected_call_trace_gas_cong >>
      simp[])
  >- ((* an exempt error is the call's *)
      rpt gen_tac >> BETA_TAC >> strip_tac >>
      `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
         fbody (es0 with gas_obs := gx) =
       (INR (Error err), ee with gas_obs := [])` by
        (qpat_x_assum `!tail. eval_stmts _ compiled_body _ = (_,_)`
           (qspec_then `[]` mp_tac) >>
         qpat_assum `!gx. eval_stmts _ compiled_body _ = _` (fn th => simp[th])) >>
      drule_all selected_call_trace_body >> strip_tac >>
      gvs[source_exempt_def]);

(* The body falls off its end: the guarded body's STOP. *)
val runtime_compose_stop_tac =
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `res = INL () /\ ~block_is_terminated sb /\ ~t.vs_halted /\
   t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    gvs[stmt_lands_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
     fbody (es0 with gas_obs := gx) = (INL (), ee with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_stmts _ compiled_body _ = (_,_)`
       (qspec_then `[]` mp_tac) >>
         qpat_assum `!gx. eval_stmts _ compiled_body _ = _` (fn th => simp[th])) >>
  `ret = NoneT` by (drule_all external_body_source_ok >> simp[]) >>
  qspecl_then [`gas_explicit_sites unit.cu_context shadow_unit.cu_context`,
               `unit.cu_context`, `cenv`, `nkey`, `ut'`, `iv`,
               `compiled_body`, `sa`, `st'`, `sb`, `func`, `t`] mp_tac
    (INST_TYPE [alpha |-> ``:256``] compile_guarded_body_stop_path) >>
  impl_tac >- gvs[] >>
  strip_tac >> qexists_tac `Halt ss` >> simp[exit_result_def] >>
  qx_genl_tac [`H1`, `G1`, `tn1`] >> strip_tac >>
  qpat_x_assum `!H cx G tn. stor_taint_ok H cx tn t ==> _`
    (qspecl_then
       [`H1`, `initial_evaluation_context am.sources am.layouts tx NONE`,
        `G1`, `tn1`] mp_tac) >>
  impl_tac >- fs[ghost_inv_at_def, stor_taint_ok_cx_dead] >>
  strip_tac >> first_assum (irule_at (Pos hd)) >>
  rpt strip_tac >>
  drule_all selected_call_trace_body >> strip_tac >> gvs[] >>
  fs[stmt_state_rel_def] >>
  drule_all external_stop_result_rel >>
  simp[abstract_machine_from_state_def];

(* The body exits through an abort, return or source halt. *)
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
val selected_call_readings_tac =
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `res <> INR (Error (RuntimeError "msg.gas: no gas reading"))` by
    (disch_tac >>
     qpat_x_assum `!tail. eval_stmts _ compiled_body _ = (_,_)`
       (qspec_then `[0w:bytes32]` mp_tac) >>
     asm_rewrite_tac[] >>
     disch_then (mp_tac o MATCH_MP eval_stmts_missing_gas_reading_empty) >>
     simp[]) >>
  `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
     fbody (es0 with gas_obs := gx) = (res, ee with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_stmts _ compiled_body _ = (_,_)`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `!gx. eval_stmts _ compiled_body _ = _` (fn th => simp[th])) >>
  drule_all selected_call_trace_body >> strip_tac >>
  namedCases_on `res` ["u", "e"]
  >- (Cases_on `u` >> gvs[]) >>
  Cases_on `e` >> gvs[AllCaseEqs()];
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

Theorem runtime_body_joint_from_start_with_readings:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
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
  runtime_body_endpoint_tac >>
  runtime_body_source_tac >>
  runtime_body_shadow_tac >>
  runtime_body_outcome_tac >>
  runtime_body_compose_tac
    (Q.ISPEC `\(cr : value + exception).
       cr <> INR (Error (RuntimeError "msg.gas: no gas reading"))`
       unit_execution_compose_result) >>
  impl_tac
  >- (runtime_compose_prefix_tac
      >- runtime_compose_stop_tac
      >- (runtime_compose_exit_tac
          >- (runtime_compose_abort_halt_cases_tac >>
              gvs[expr_exit_def, external_call_result_rel_def] >>
              runtime_compose_halt_tac)
          >> gvs[abstract_machine_from_state_def])
      >> selected_call_readings_tac) >>
  runtime_selected_readings_finish_tac
    ((qexistsl_tac [`shadow_unit`,`marks`] >>
      conj_tac >- first_assum ACCEPT_TAC), ALL_TAC)
QED

Theorem runtime_body_joint_from_start_with_shadow:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
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
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
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
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
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

Theorem external_lock_failure_trace[local]:
  source_deployment_rel tops am tx /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  send_call_value mut cx
    (initial_state am [env] with <|outcomes := SOME os; requests := []|>) =
      (INL (),es0) /\
  lock_if_nr cx T (is_view_mut mut) es0 = (INR exc,es_abort) ==>
  !gs. call_external_trace (SOME os) gs am tx =
    (INR exc,am,[],[StorageLock global_nonreentrant_slot])
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    (drule_all selected_nonreentrant_lock_metadata >> simp[]) >>
  `es0.storage_trace = [] /\ es0.requests = []` by
    (drule send_call_value_accounts >> simp[initial_state_def]) >>
  `es_abort.storage_trace = [StorageLock global_nonreentrant_slot] /\
    es_abort.requests = []` by
    (Cases_on `lookup_storage (n2w global_nonreentrant_slot)
       (es0.tStorage cx.txn.target) = 1w` >>
     Cases_on `is_view_mut mut` >> Cases_on `cx.txn.is_static` >>
     gvs[lock_if_nr_def,
         nonreentrantEquivTheory.acquire_nonreentrant_lock_execution,
         check_not_static_def, vyperStateTheory.check_def,
         vyperStateTheory.assert_def, vyperStateTheory.ignore_bind_def,
         vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def]) >>
  `LENGTH tx.args = LENGTH args` by (drule bind_arguments_length >> simp[]) >>
  gen_tac >>
  `lock_if_nr cx T (is_view_mut mut) (es0 with gas_obs := gs) =
    (INR exc,es_abort with gas_obs := gs)` by
    (drule lock_if_nr_with_gas_obs >> simp[Excl "lock_if_nr_def"]) >>
  qpat_x_assum `cx = initial_evaluation_context _ _ _ _` SUBST_ALL_TAC >>
  drule_all call_external_selected_lock_failure >>
  simp[Excl "lock_if_nr_def"]
QED

Theorem runtime_lock_abort_result_with:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,T,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
       <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) /\
  lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
    T (is_view_mut mut) es0 = (INR exc,es_abort) /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions =
    SOME func /\
  fn_entry_label func = SOME "__entry" /\
  lookup_block "__entry" func.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 /\
  expr_exit (INR exc : unit + exception) (Abort a t) /\
  (exc = Error (RuntimeError "nonreentrant lock") \/
   exc = Error (RuntimeError "write in static context")) /\
  (!D explicit. gas_origin_ptr_path
     (D,0,explicit,unit.cu_context,func,[])
     (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>,FEMPTY,entry_taint) [] (Abort a t,G,tn)) ==>
  ?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  source_unit_execution_correct_with shadow_unit.cu_context [] tops ret am tx unit vs /\
  (!gs. FST (call_external (SOME vs.vs_outcomes) gs am tx) <>
    INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `!gs. call_external_trace (SOME vs.vs_outcomes) gs am tx =
    (INR exc,am,[],[StorageLock global_nonreentrant_slot])` by
    (mp_tac (Q.INST [`cx` |->
       `initial_evaluation_context am.sources am.layouts tx NONE`,
       `os` |-> `vs.vs_outcomes`] (SPEC_ALL external_lock_failure_trace)) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
  `?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
                gas_shadow_unit unit shadow_unit` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     irule runtime_gas_shadow_unit_exists >> simp[] >>
     drule loweringShapePropsTheory.supported_program_no_external_defaults >> simp[]) >>
  pop_assum strip_assume_tac >>
  qexists_tac `shadow_unit` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (gen_tac >>
      qpat_x_assum `!gs. call_external_trace _ gs _ _ = _`
        (qspec_then `gs` (mp_tac o MATCH_MP call_external_trace_result)) >>
      Cases_on `exc = Error (RuntimeError "nonreentrant lock")` >> gvs[]) >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    fs[gas_shadow_unit_def] >>
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
  disj2_tac >> qexistsl_tac
    [`INR exc`,`am`,`[]`,`[StorageLock global_nonreentrant_slot]`] >>
  simp[] >>
  disj2_tac >> qexists_tac `Abort a t` >>
  conj_tac >- simp[exit_result_def] >>
  conj_tac
  >- simp[storage_trace_domain_def, valid_horizon_def,
          storage_trace_horizon_def, storage_trace_regions_def,
          storage_trace_locks_def, storage_observations_ok_def,
          regions_consistent_def, storage_locks_separated_def,
          storage_well_formed_on_def, storage_roots_fit_def,
          storage_trace_backends_well_formed_def,
          contextTheory.global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  `!D. gas_origin_ptr_path
     (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
      unit.cu_context,func,[]) (entry,FEMPTY,entry_taint) [] (Abort a t,G,tn)` by
    (gen_tac >> qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
      (qspecl_then [`D`,`gas_explicit_sites unit.cu_context shadow_unit.cu_context`]
        ACCEPT_TAC)) >>
  conj_tac >-
    (qpat_assum `!D. gas_origin_ptr_path _ (entry,_,_) _ _`
       (mp_tac o CONJUNCT1 o MATCH_MP gas_origin_ptr_path_projections o Q.SPEC `ARB:dead`) >>
     simp[Abbr `entry`]) >>
  rpt gen_tac >> strip_tac >>
  conj_tac >-
    (qpat_assum `exc = _ \/ exc = _` (DISJ_CASES_THEN SUBST1_TAC) >>
     simp[external_call_result_rel_def]) >>
  qpat_assum `!D. gas_origin_ptr_path _ (entry,_,_) _ _`
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

Theorem lower_vyper_runtime_unit_correct:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >> selected_entry_split_tac
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all lower_vyper_runtime_unit_body_joint >>
      disch_then (qx_choosel_then [`shadow_ctx`, `func`, `shadow_func`, `marks`]
        (MAP_EVERY ASSUME_TAC o CONJUNCTS)) >>
      pure_rewrite_tac[source_unit_execution_correct_def,
                       source_unit_execution_correct_at_def] >>
      qexists_tac `marks` >>
      qexistsl_tac [`shadow_ctx`, `func`, `shadow_func`] >> simp[]) >>
  irule external_entry_value_revert >> metis_tac[]
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
      outcomes_accounts_typed (SOME vs.vs_outcomes) /\
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
  impl_tac >- simp[] >>
  simp[source_unit_execution_correct_def,
       source_unit_execution_correct_at_def] >>
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
    by metis_tac[lower_vyper_runtime_unit_block_phi, entry_runtime_no_dalloca] >>
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

(* Prepare the body at the state immediately after its entry lock. *)
val runtime_locked_body_outcome_tac =
  drule (Q.INST [`E` |-> `module_consts_env tops []`] runtime_package_source_body) >>
  strip_tac >>
  `LENGTH tx.args = LENGTH args` by
    (drule bind_arguments_length >> simp[]) >>
  drule_all externalEntryJointTheory.selected_nonreentrant_lock_metadata >>
  strip_tac >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[contextTheory.global_nonreentrant_slot_def,wordsTheory.dimword_def] >>
  drule_all external_source_body_frame_nr >> strip_tac >>
  mp_tac (Q.INST [`nr` |-> `T`, `os` |-> `vs.vs_outcomes`]
    external_source_body_substitution_nr) >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  runtime_compiled_body_abi_targets_tac >>
  qabbrev_tac `compiled_body = subst_consts_stmts (module_consts_env tops []) fbody` >>
  mp_tac (Q.SPECL [`tops`,`rpolicy`,`unit`,`lbl`,`cenv0`,`pos_args`,
    `min_cds`,`is_payable`,`T`,`global_nonreentrant_slot`,`T`,`mut = View`,
    `compiled_body`,`rt`,`st`,`cenv`,`sa`,`sl`,`st'`,`bindings`,
    `unit.cu_context`,
    `initial_evaluation_context am.sources am.layouts tx NONE`,
    `env_t`,`env'`,`ret`] runtime_entry_body_shadow_with_shadow_nr) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`func2`,`shadow_ctx`,`shadow_func`,`cenv'`,
    `sb`,`shadow_sl`,`shadow_sb`,`shadow_unit`] strip_assume_tac) >>
  `func2 = func` by gvs[] >>
  drule_all guarded_body_stmts_env >>
  disch_then (qx_choose_then `compiled_env` assume_tac) >>
  `se = sb` by gvs[] >>
  `compiled_env = cenv'` by gvs[] >>
  qpat_x_assum `func2 = func` SUBST_ALL_TAC >>
  qpat_x_assum `se = sb` SUBST_ALL_TAC >>
  qpat_x_assum `compiled_env = cenv'` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_ctx = shadow_unit.cu_context` SUBST_ALL_TAC;

val runtime_locked_return_frame_tac =
  mp_tac (Q.SPECL
    [`\H. cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)`,
     `0`, `NONE`, `shadow_unit.cu_context`, `[]`, `func`, `shadow_func`,
     `tops`, `rpolicy`, `unit`, `am`, `tx`, `ret`, `mut`, `T`, `args`, `fbody`,
     `env`, `source_lbl`, `cenv0`, `pos_args`, `min_cds`, `is_payable`,
     `global_nonreentrant_slot`, `T`, `mut = View`, `rt`, `st`, `cenv`, `sa`]
    external_source_frame_ret_ok_full_nr) >>
  impl_tac >- simp[] >> disch_then assume_tac >>
  `cx_tops (initial_evaluation_context am.sources am.layouts tx NONE) = tops` by
    (irule cx_tops_module >>
     gvs[source_deployment_rel_def, vyperContextTheory.get_module_code_def,
         initial_evaluation_context_def]) >>
  `~cenv.ce_is_ctor` by
    gvs[bodySimTheory.body_inv_def, initial_evaluation_context_def] >>
  `~ctx_has_dalloca unit.cu_context` by
    metis_tac[entry_runtime_no_dalloca] >>
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule_all caller_runtime_entry_integrity >> simp[]) >>
  `struct_args_unique tops` by
    (fs[source_typing_ok_def] >> metis_tac[checked_contract_struct_args_unique]);

Theorem runtime_locked_well_formed_on[local]:
  send_call_value mut cx
    (initial_state am [env] with <|outcomes := orc; requests := []|>) =
    (INL (),es0) /\
  lock_if_nr cx T iv es0 = (INL (),es_lock) ==>
  !H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
    storage_well_formed_on cx es_lock (FST H)
Proof
  strip_tac >> gen_tac >> simp_tac std_ss [valid_horizon_def] >> strip_tac >>
  `storage_well_formed_on cx es0 (FST H)` by
    (qpat_assum `send_call_value _ _ _ = _` (fn th =>
       mp_tac (Q.INST [`R` |-> `FST (H : (bool # bytes32 # type_value) list # num list)`]
         (MATCH_MP (INST_TYPE [alpha |-> ``:256``] body_start_storage_well_formed) th))) >>
     simp[]) >>
  match_mp_tac (Q.INST [`st` |-> `es0`,
                       `H` |-> `(H : (bool # bytes32 # type_value) list # num list)`,
                       `nr` |-> `T`,
                       `view` |-> `iv`, `res` |-> `INL ()`]
    vyperExternalEntryStorageFrameTheory.lock_if_nr_preserves_storage_well_formed_on) >>
  asm_rewrite_tac[]
QED

(* Obligation shared by the successful and reverting terminal paths. *)
val runtime_locked_eval_tac =
  `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
     fbody (es_lock with gas_obs := gx) = (res, ee with gas_obs := [])` by
    (qpat_x_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _` (fn th => simp[th])) >>
  `stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)` by
    (drule_all external_body_source_ok_nr >> simp[]);

val runtime_locked_unlock_tac =
  mp_tac (Q.INST [`nr` |-> `T`, `iv` |-> `is_view_mut mut`,
    `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
    `es` |-> `ee with gas_obs := []`, `key` |-> `global_nonreentrant_slot`]
      (SPEC_ALL unlock_if_nr_success_trace)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `eu` strip_assume_tac) >>
  drule_all selected_call_trace_result_nr >> strip_tac;

Theorem runtime_selected_lock_readings:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 es_lock source_lbl lbl cenv0 pos_args min_cds is_payable
   rt st cenv sa sl se st' func s0 G0 tn0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, T, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      T (is_view_mut mut) es0 = (INL (),es_lock) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,T,lookup_raw_return_or_F (NONE:num option)
           tx.function_name External tops,tx.function_name,args,[],ret,
           subst_consts_stmts (module_consts_env tops []) fbody)) =
      (source_lbl,cenv0,pos_args,min_cds,is_payable,T,global_nonreentrant_slot,
        T,mut = View,subst_consts_stmts (module_consts_env tops []) fbody,rt) /\
    runtime_entry_body_start tops rpolicy
      (lbl,cenv0,pos_args,min_cds,is_payable,T,global_nonreentrant_slot,
        T,mut = View,subst_consts_stmts (module_consts_env tops []) fbody,rt) st /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) /\
    compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) sa =
      ((),sl) /\
    compile_guarded_body cenv T global_nonreentrant_slot T (mut = View)
      (subst_consts_stmts (module_consts_env tops []) fbody) rt sa = ((),st') /\
    compile_stmts cenv NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT)
      (subst_consts_stmts (module_consts_env tops []) fbody) sl = ((),se) /\
    fn_has_code sl se func /\ fn_has_code se st' func /\
    fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sl /\ ~block_is_terminated sl /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    alloca_history func s0 /\ fresh_vars_wrt sl s0 /\
    return_buf_frame NONE cenv sl s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sl.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sl.cs_current_insts /\
    s0.vs_gas_readings = vs.vs_gas_readings /\
    s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
    (mut <> View ==> ~tx.is_static) /\
    (!st0 H. valid_horizon
      (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
      es_lock.storage_trace ==>
      ((!fuel. ptr_safe_run
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 fuel unit.cu_context func [] G0 tn0 s0) ==>
        !fuel. ptr_safe_blocks
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 fuel unit.cu_context func [] FEMPTY entry_taint
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0 |>)) /\
      ghost_inv_at
        (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
        0 NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE)
        es_lock G0 tn0 s0 /\
      stmt_state_rel H unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es_lock s0 /\
      !explicit.
        gas_origin_ptr_path
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
           0,explicit,unit.cu_context,func,[])
          (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0 |>,FEMPTY,entry_taint) [] (OK s0,G0,tn0))
    ==>
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
  rpt strip_tac >>
  runtime_locked_body_outcome_tac >>
  runtime_locked_return_frame_tac >>
  qpat_assum `send_call_value _ _ _ = (INL (),es0)` (fn send =>
    qpat_assum `lock_if_nr _ T _ es0 = (INL (),es_lock)` (fn lock =>
      assume_tac (MATCH_MP runtime_locked_well_formed_on (CONJ send lock)))) >>
  runtime_shadow_body_inv_tac >>
  drule_at (Pat `frame_ret_ok_full _ _ _ _ _`) body_stmts_sim_full >>
  disch_then (qspecl_then [`tops`, `bindings`, `env_t`, `env'`, `NoLoop`,
                           `compiled_body`, `es_lock`] mp_tac) >>
  impl_tac
  >- (simp[] >> metis_tac[]) >>
  disch_then (mp_tac o REWRITE_RULE [stmt_frag_full_def]) >>
  disch_then (qspecl_then [`initial_state am []`, `sl`, `sb`, `shadow_sl`,
                           `shadow_sb`, `s0`, `G0`, `tn0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (`cenv.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
      simp[dead_lo_ok_def, ret_pc_ok_def, return_buf_sep_def, gas_admissible_def] >>
      rpt strip_tac
      >~ [`stmt_res_ok`] >- metis_tac[external_body_source_ok_nr]
      >~ [`dalloca_no_wrap`]
      >- metis_tac[bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap]
      >> qpat_x_assum `!st0 H. valid_horizon _ _ _ es_lock.storage_trace ==> _`
           drule >> simp[]) >>
  qpat_assum `cx_tops _ = tops` (fn th => REWRITE_TAC [th]) >>
  strip_tac >>
  runtime_body_compose_tac
    (Q.ISPEC `\(cr : value + exception).
       cr <> INR (Error (RuntimeError "msg.gas: no gas reading"))`
       unit_execution_compose_result_horizon) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[evaluate_storage_trace_frame]
      >- (`es0.storage_trace = []` by
            (drule send_call_value_accounts >> simp[initial_state_def]) >>
          `es_lock.storage_trace = [StorageLock global_nonreentrant_slot]` by
            (drule_all lock_if_nr_success_trace >> simp[]) >>
          simp[storage_trace_domain_def, valid_horizon_def,
               storage_trace_horizon_def, storage_trace_regions_def,
               storage_trace_locks_def, regions_consistent_def,
               storage_locks_separated_def, storage_well_formed_on_def,
               storage_observations_ok_def, storage_roots_fit_def,
               storage_trace_backends_well_formed_def, arithmeticTheory.ADD1])
      >- (rpt strip_tac >> BETA_TAC >>
          qpat_x_assum `!st0 H. valid_horizon _ _ _ es_lock.storage_trace ==> _`
            drule >> strip_tac >> fs[])
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          mp_tac (Q.INST [`nr` |-> `T`, `iv` |-> `is_view_mut mut`,
            `cx` |-> `initial_evaluation_context am.sources am.layouts tx NONE`,
            `es` |-> `ee`, `key` |-> `global_nonreentrant_slot`]
              (SPEC_ALL unlock_if_nr_success_trace)) >>
          impl_tac >- simp[] >> strip_tac >>
          qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _`
            (qspec_then `gobs` (fn eq =>
              qpat_assum `eval_stmts _ compiled_body _ = (res,ee)`
                (assume_tac o REWRITE_RULE [eq]))) >>
          drule_all selected_call_trace_result_nr >> strip_tac >>
          qpat_assum `call_external_trace _ gobs _ _ = (_,_,_,obs)`
            (fn trace => simp_tac (srw_ss()) [trace]) >>
          Cases_on `res = INL () \/ (?v. res = INR (ReturnException v))`
          >- (qpat_assum `_ ==> obs = se.storage_trace` (fn trace =>
                first_assum (SUBST1_TAC o MATCH_MP trace)) >>
              drule_all selected_unlock_trace_horizons >>
              disch_then (qspec_then `initial_state am []` ACCEPT_TAC)) >>
          qpat_assum `_ ==> obs = ee.storage_trace` (fn trace =>
            first_assum (SUBST1_TAC o MATCH_MP trace)) >> simp[])
      >- (rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
          runtime_locked_eval_tac >>
          qspecl_then [`tops`, `am`, `tx`, `ret`, `mut`, `T`, `args`, `fbody`,
                       `env`, `vs.vs_outcomes`, `gx ++ tail`, `gx`, `es0`,
                       `es_lock`, `res`, `ee`, `tail`, `[]`] mp_tac
            selected_call_trace_gas_cong_nr >> simp[] >>
          disch_then irule >>
          qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _`
            (qspec_then `gx ++ tail` (fn eq => REWRITE_TAC [GSYM eq])) >>
          qpat_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
            (qspec_then `tail` ACCEPT_TAC))
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
             fbody (es_lock with gas_obs := gx) =
           (INR (Error err), ee with gas_obs := [])` by
            (qpat_x_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
               (qspec_then `[]` mp_tac) >>
             qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _` (fn th => simp[th])) >>
          runtime_locked_unlock_tac >> gvs[source_exempt_def])
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          `res = INL () /\ ~block_is_terminated sb /\ ~t.vs_halted /\
           t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts` by
            gvs[stmt_lands_def] >>
          runtime_locked_eval_tac >>
          `ret = NoneT` by simp[] >>
          qpat_x_assum `cx_tops _ = tops` kall_tac >>
          rpt BasicProvers.VAR_EQ_TAC >>
          mp_tac (Q.INST [`nr` |-> `T`, `nkey` |-> `global_nonreentrant_slot`,
                          `iv` |-> `mut = View`, `stmts` |-> `compiled_body`, `st` |-> `sa`,
                          `sl` |-> `sl`, `se` |-> `sb`, `sb` |-> `st'`, `cenv` |-> `cenv`]
            nonreentrantExitTheory.compile_guarded_body_stop_unlock_parts) >>
          impl_tac >- fs[] >>
          disch_then (qx_choose_then `su` strip_assume_tac) >>
          `fn_has_code sb su func /\ fn_has_code su st' func` by
            metis_tac[fn_has_code_split] >>
          `allocas_from 0 t` by simp[ptrDisciplineTheory.allocas_from_def] >>
          qexists_tac `Halt (halt_state ((if mut <> View then
            tstore (n2w global_nonreentrant_slot) 0w t else t)
            with <|vs_inst_idx := LENGTH su.cs_current_insts;
                   vs_returndata := []|>))` >>
          simp[exit_result_def] >>
          qx_genl_tac [`H1`, `G1`, `tn1`] >> strip_tac >>
          `mut <> View ==> ~t.vs_call_ctx.cc_static` by
            fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
               loweringStateRelDefsTheory.call_ctx_rel_def,
               initial_evaluation_context_def] >>
          (* The halt state of this fixed instruction suffix precedes H and ghosts. *)
          mp_tac (Q.INST [`nr` |-> `T`, `iv` |-> `mut = View`,
               `nkey` |-> `global_nonreentrant_slot`, `st` |-> `sb`,
               `sb` |-> `st'`, `s` |-> `t`, `ctx` |-> `unit.cu_context`,
               `tn` |-> `tn1`, `lo` |-> `0`, `G` |-> `G1`,
               `PG` |-> `[]`, `DF` |-> `\H. cx_dead H
                  (initial_evaluation_context am.sources am.layouts tx NONE)`,
               `cenv` |-> `cenv'`, `cx` |->
                  `initial_evaluation_context am.sources am.layouts tx NONE`]
               (INST_TYPE [alpha |-> ``:256``]
               nonreentrantExitTheory.optional_transient_unlock_stop_joint_at)) >>
          impl_tac >- simp[] >>
          disch_then (qx_choosel_then [`ss`,`tn'`] strip_assume_tac) >>
          qpat_assum `ss = _` (fn eq =>
            PURE_REWRITE_TAC [GSYM (SIMP_RULE bool_ss [] eq)]) >>
          qexistsl_tac [`G1`,`tn'`] >>
          conj_tac
          >- (`~cenv'.ce_is_ctor` by
                (qpat_assum `cenv_top_ext cenv cenv' _`
                   (mp_tac o MATCH_MP stmtFragPtrTheory.cenv_top_ext_is_ctor) >> simp[]) >>
              qpat_assum `ghost_inv_at _ 0 NONE cenv' _ _ G1 tn1 t`
                (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
              qpat_assum `!H explicit. dead_lo_ok _ _ _ _ _ /\ _ ==> _`
                (irule o BETA_RULE) >>
              simp[dead_lo_ok_def]) >>
          rpt strip_tac >>
          runtime_locked_unlock_tac >>
          `unlock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
             T (is_view_mut mut) =
           if mut <> View then release_nonreentrant_lock tx.target global_nonreentrant_slot
           else vyperState$return ()` by
            (Cases_on `mut = View` >> gvs[unlock_if_nr_def,initial_evaluation_context_def]) >>
          drule_all source_typing_none_return_plain >> strip_tac >>
          fs[stmt_state_rel_def] >>
          qspecl_then [`H1`,`func`,`cenv'`,
            `initial_evaluation_context am.sources am.layouts tx NONE`,
            `ee with gas_obs := []`,`eu`,`t`,`ss`,`T`,`global_nonreentrant_slot`,
            `mut = View`,`tops`,`tx`,`am.sources`,`am.exports`,`am.layouts`] mp_tac
              external_halt_success_unlock >>
          impl_tac
          >- (conj_tac >- simp[loweringStateRelDefsTheory.state_rel_gas_obs] >>
              simp[initial_evaluation_context_def]) >>
          strip_tac >>
          gvs[external_call_result_rel_def, tx_return_bytes_def, return_bytes_def,
              abstract_machine_from_state_def, finalize_pending_deletions_def])
      >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
          runtime_locked_eval_tac >>
          runtime_locked_unlock_tac >>
          qpat_x_assum `!tail. stmt_exit_ptr _ _ _ _ _`
            (qspec_then `[]` mp_tac) >>
          simp[stmt_exit_ptr_def] >> strip_tac
          >- (runtime_compose_abort_halt_cases_tac >>
              gvs[expr_exit_def, external_call_result_rel_def] >>
              runtime_compose_halt_tac) >>
          `(abstract_machine_from_state am.sources am.exports am.layouts
               (eu with scopes := [])) =
             abstract_machine_from_state am.sources am.exports am.layouts eu` by
            simp[abstract_machine_from_state_def] >>
          qpat_assum `unlock_if_nr _ T _ (ee with gas_obs := []) = (INL (),eu)`
            (mp_tac o MATCH_MP (Q.INST [`sc` |-> `[]`] unlock_if_nr_with_scopes)) >>
          simp[] >> strip_tac >> gvs[])
      >> ((* The selected source call forwards a missing-reading error only from
             the body, which has consumed exactly the marked readings. *)
          qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
          rpt gen_tac >> BETA_TAC >> strip_tac >>
          `res <> INR (Error (RuntimeError "msg.gas: no gas reading"))` by
            (disch_tac >>
             qpat_x_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
               (qspec_then `[0w:bytes32]` mp_tac) >>
             asm_rewrite_tac[] >>
             disch_then (mp_tac o MATCH_MP eval_stmts_missing_gas_reading_empty) >>
             simp[]) >>
          `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
             fbody (es_lock with gas_obs := gx) = (res, ee with gas_obs := [])` by
            (qpat_x_assum `!rest. eval_stmts _ compiled_body _ = (_,ee with gas_obs := rest)`
               (qspec_then `[]` mp_tac) >>
             qpat_assum `!gas. eval_stmts _ compiled_body _ = eval_stmts _ fbody _` (fn th => simp[th])) >>
          runtime_locked_unlock_tac >>
          `cr = r` by
            (qpat_assum `call_external_trace _ gx _ _ = (cr,_,_,_)` (fn trace =>
               qpat_assum `call_external_trace _ gx _ _ = (r,_,_,_)`
                 (mp_tac o REWRITE_RULE [trace])) >> simp[]) >>
          pop_assum SUBST1_TAC >>
          (* Only the source result laws matter for this case split. *)
          MAP_EVERY (fn pat => qpat_assum pat mp_tac)
            [`res <> INR (Error (RuntimeError "msg.gas: no gas reading"))`,
             `res = INL () ==> r = _ /\ _`,
             `!v. res = INR (ReturnException v) ==> _`,
             `res = INR HaltException ==> r = _ /\ _`,
             `!e. res = INR e /\ _ ==> r = _ /\ _`] >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          namedCases_on `res` ["u", "e"]
          >- (Cases_on `u` >> simp[]) >>
          Cases_on `e` >> simp[AllCaseEqs()] >> strip_tac >> gvs[])) >>
  runtime_selected_readings_finish_tac
    ((qexistsl_tac [`shadow_unit`,`marks`] >>
      conj_tac >- first_assum ACCEPT_TAC), ALL_TAC)
QED

Theorem lower_vyper_runtime_unit_correct_readings_available:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) ==>
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
  selected_entry_split_tac
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all external_entry_joint_endpoint >> strip_tac >>
      drule_all runtime_body_joint_from_start_with_readings >>
      disch_then (qx_choosel_then [`shadow_unit`,`marks`] strip_assume_tac) >>
      qexists_tac `marks` >>
      metis_tac[source_unit_execution_correct_at_with]) >>
  drule_all external_entry_value_revert >>
  rewrite_tac[source_unit_execution_correct_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >>
  qexists_tac `marks` >> simp[] >>
  `value_transfer_ok tx am.accounts` by fs[initial_venom_state_rel_def] >>
  drule_all external_entry_reject_readings >> simp[]
QED
