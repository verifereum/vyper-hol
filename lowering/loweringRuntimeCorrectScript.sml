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
 *)

Theory loweringRuntimeCorrect
Ancestors
  sourceUnitExecution e2eDefs compileVyper vyperInterpreter vyperState
  vyperStorageFootprint gasShadowUnit vyperTypeSelectedEntrySoundness
  externalEntryValueRevert unitExecutionCompose externalEntryJoint
  externalBodyFrame externalFrameRetOk runtimeBodyShadow
  externalCallSelected externalBodySourceOk bodySimFullMain bodySimFull
  entryStateRel entryReachBodyFmp entryReachBodyRuntimeResources
  bodyAbiDecodeTarget rawReturnHeader loweringHalt gasContext bodyPtrDefs
  gasOutcomeFull fragGasOriginPtr loweringPosts stmtSimDefs exprSimDefs
  exprLoweringProps vyperStorageTrace vyperStorageBackend vyperCall
  fragExec moduleLowering

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
  drule_all call_external_selected_body_trace >> strip_tac >>
  qexistsl_tac [`r`, `am'`, `rqs`] >> simp[] >>
  drule call_external_trace_result >> strip_tac >>
  drule_all call_external_selected_body_gas >>
  disch_then (qspec_then `gx` assume_tac) >>
  `es0.scopes = [env]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  `(es0 with gas_obs := gx).scopes = [env]` by simp[] >>
  drule_all call_external_body_run >>
  disch_then (qspecl_then [`am`, `mut`, `type_env tops`, `ret`]
                strip_assume_tac) >>
  rpt conj_tac
  >- (strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!v. res = INR (ReturnException v) ==> _`
        (qspec_then `v` mp_tac) >>
      gvs[] >> strip_tac >> gvs[] >> every_case_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!e. res = INR e /\ _ ==> _` (qspec_then `e` mp_tac) >>
  simp[] >> strip_tac >> Cases_on `e` >> gvs[]
QED

(* The selected call is the same at two gas observations at which the body
   runs alike. *)
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
  gvs[abstract_machine_from_state_def] >> every_case_tac >> gvs[]
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
     combinTheory.APPLY_UPDATE_THM]
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
     simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, comp_get_def, emitHelperTheory.emit_inst_def,
          fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst sb.cs_next_id STOP [] []) t =
          Halt (halt_state (t with vs_returndata := []))` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs] >>
  `!fuel. gas_count_step fuel ctx (mk_inst sb.cs_next_id STOP [] []) t = 0` by
    simp[gas_count_step_def, mk_inst_def] >>
  `!fuel. gas_events_step fuel ctx func.fn_name
            (mk_inst sb.cs_next_id STOP [] []) t = []` by
    metis_tac[cj 1 gas_events_length, LENGTH_NIL] >>
  `!fuel. mem_safe_step fuel ctx (mk_inst sb.cs_next_id STOP [] []) t` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
  qexists_tac `halt_state (t with vs_returndata := [])` >>
  rpt conj_tac >~ [`gas_origin_ptr_path`]
  >- (rpt strip_tac >> qexistsl_tac [`G`, `tn`] >>
      `!fuel. ptr_safe_step (cx_dead H cx) 0 fuel ctx func [] G tn
                (mk_inst sb.cs_next_id STOP [] []) t` by
        (gen_tac >> simp[ptr_safe_step_def, ptr_inst_ok_def] >>
         gvs[access_ok_def, taint_ok_def, allocas_from_def,
             source_memory_read_ranges_def,
             codegenRelTheory.source_memory_write_ranges_def, mk_inst_def,
             step_taint_def, store_taint_def, adopt_reset_def,
             imm_taint_def, ret_taint_def, halt_state_def,
             stor_taint_ok_def, cx_dead_def]) >>
      irule (cj 3 gas_origin_ptr_path_rules) >>
      simp[exit_result_def, gas_origin_ptr_edge_def] >> conj_tac
      >- (simp[gas_origin_edge_def] >>
          qexistsl_tac [`0`, `bb`, `mk_inst sb.cs_next_id STOP [] []`] >>
          simp[]) >>
      simp[gas_path_ptr_edge_def] >>
      qexistsl_tac [`0`, `bb`, `mk_inst sb.cs_next_id STOP [] []`] >>
      simp[]) >>
  simp[halt_state_def]
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
  simp[external_call_result_rel_def, tx_return_bytes_def, return_bytes_def]
QED

(* ===== S1 ===== *)

(* S1 when the value moves and the body starts: unit_execution_compose of
   the entry's pointer path to the body's start and the body's
   gas_outcome_full, the call being call_external_trace at the call's
   outcomes. *)
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
           ~(source_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail) /\
             call_outcomes_storage_ok am tx vs.vs_outcomes
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
  rpt gen_tac >> strip_tac >>
  `LENGTH tx.args = LENGTH args` by
    (drule bind_arguments_length >> simp[]) >>
  drule_all external_entry_joint >> strip_tac >>
  drule_all external_body_frame >> strip_tac >>
  `rt = if ret = NoneT then NONE else SOME ret` by
    gvs[package_external_fn_def, set_external_package_target_def] >>
  drule guarded_body_code >> strip_tac >>
  drule_all guarded_body_stmts_env >> strip_tac >>
  drule_all runtime_selected_body_shadow >>
  disch_then (qx_choosel_then [`func2`, `shadow_ctx`, `shadow_func`,
                `cenv2`, `sb2`, `shadow_sa`, `shadow_sb`] strip_assume_tac) >>
  `func2 = func /\ cenv2 = cenv' /\ sb2 = sb` by gvs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  drule_all external_frame_ret_ok_full >>
  disch_then (qspecl_then
    [`\H. cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)`,
     `0`, `NONE`, `shadow_ctx`, `[]`, `func`, `shadow_func`] assume_tac) >>
  `cx_tops (initial_evaluation_context am.sources am.layouts tx NONE) =
   tops` by
    (irule cx_tops_module >>
     gvs[source_deployment_rel_def, get_module_code_def,
         initial_evaluation_context_def]) >>
  `~cenv.ce_is_ctor` by
    gvs[bodySimTheory.body_inv_def, initial_evaluation_context_def] >>
  `~ctx_has_dalloca unit.cu_context` by
    metis_tac[entry_runtime_no_dalloca] >>
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule_all caller_runtime_entry_integrity >> simp[]) >>
  (* the body *)
  drule_at (Pat `frame_ret_ok_full _ _ _ _ _`) body_stmts_sim_full >>
  disch_then (qspecl_then [`tops`, `bindings`, `env_t`, `env'`, `NoLoop`,
                           `fbody`, `es0`] mp_tac) >>
  impl_tac
  >- (simp[] >> metis_tac[lookup_function_abi_decode_target_occurs]) >>
  disch_then (mp_tac o REWRITE_RULE [stmt_frag_full_def]) >>
  disch_then (qspecl_then [`initial_state am []`, `sa`, `sb`, `shadow_sa`,
                           `shadow_sb`, `s0`, `G0`, `tn0`, `cenv'`] mp_tac) >>
  impl_tac
  >- (`cenv.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
      simp[dead_lo_ok_def, ret_pc_ok_def, gas_admissible_def] >>
      rpt strip_tac
      >~ [`stmt_res_ok`] >- metis_tac[external_body_source_ok]
      >~ [`storage_well_formed_on`]
      >- (drule body_start_storage_well_formed >> fs[valid_horizon_def])
      >> qpat_x_assum `!st0 H. valid_horizon _ _ _ es0.storage_trace ==> _`
           drule >> simp[]) >>
  qpat_assum `cx_tops _ = tops` (fn th => REWRITE_TAC [th]) >>
  strip_tac >>
  (* the unit *)
  drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) unit_execution_compose >>
  disch_then (qspecl_then
    [`vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0 |>`,
     `\g. call_external_trace (SOME vs.vs_outcomes) g am tx`,
     `\H c r. external_call_result_rel H tops ret tx c r`,
     `source_exempt tops`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac
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
            drule >> simp[])
      >- ((* the observations are the body's *)
          rpt gen_tac >> BETA_TAC >> strip_tac >>
          drule_all selected_call_trace_body >> strip_tac >> simp[])
      >- ((* the call does not depend on the unread readings *)
          rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
          `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
             fbody (es0 with gas_obs := gx) = (res, ee with gas_obs := [])` by
            (qpat_x_assum `!tail. eval_stmts _ _ _ = _`
               (qspec_then `[]` mp_tac) >> simp[]) >>
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
            (qpat_x_assum `!tail. eval_stmts _ _ _ = _`
               (qspec_then `[]` mp_tac) >> simp[]) >>
          drule_all selected_call_trace_body >> strip_tac >>
          gvs[source_exempt_def])
      >- ((* the body falls off its end: the guarded body's STOP *)
          rpt gen_tac >> BETA_TAC >> strip_tac >>
          `res = INL () /\ ~block_is_terminated sb /\ ~t.vs_halted /\
           t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts` by
            gvs[stmt_lands_def] >>
          rpt BasicProvers.VAR_EQ_TAC >>
          `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
             fbody (es0 with gas_obs := gx) = (INL (), ee with gas_obs := [])` by
            (qpat_x_assum `!tail. eval_stmts _ _ _ = _`
               (qspec_then `[]` mp_tac) >> simp[]) >>
          `ret = NoneT` by (drule_all external_body_source_ok >> simp[]) >>
          `rt = NONE` by simp[] >>
          qspecl_then [`gas_explicit_sites unit.cu_context shadow_ctx`,
                       `unit.cu_context`, `cenv`, `nkey`, `ut'`, `iv`,
                       `fbody`, `sa`, `st'`, `sb`, `func`, `t`] mp_tac
            compile_guarded_body_stop_path >>
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
          irule external_stop_result_rel >>
          gvs[stmt_state_rel_def] >> metis_tac[]) >>
      (* the body exits: an abort, or a return *)
      rpt gen_tac >> BETA_TAC >> strip_tac >>
      `eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
         fbody (es0 with gas_obs := gx) = (res, ee with gas_obs := [])` by
        (qpat_x_assum `!tail. eval_stmts _ _ _ = _`
           (qspec_then `[]` mp_tac) >> simp[]) >>
      `stmt_res_ok NoLoop res` by
        (drule_all external_body_source_ok >> simp[]) >>
      drule_all selected_call_trace_body >> strip_tac >>
      qpat_x_assum `!tail. stmt_exit_ptr _ _ _ _ _`
        (qspec_then `[]` mp_tac) >>
      simp[stmt_exit_ptr_def] >> strip_tac
      >- (qpat_x_assum `stmt_res_ok _ _`
            (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_res_ok_def]) >>
          gvs[] >> Cases_on `r` >>
          gvs[expr_exit_def, external_call_result_rel_def]) >>
      gvs[abstract_machine_from_state_def]) >>
  strip_tac >>
  qexistsl_tac [`shadow_ctx`, `func`, `shadow_func`, `marks`] >> simp[] >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[call_external_trace_observations] >> strip_tac
  >- (disj1_tac >> conj_tac
      >- (gen_tac >> strip_tac >>
          qpat_x_assum `!tail. ~storage_trace_domain _ _ _`
            (qspec_then `tail` mp_tac) >>
          simp[source_storage_guards_domain])
      >> metis_tac[]) >>
  disj2_tac >> first_assum ACCEPT_TAC
QED

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
  rpt strip_tac >>
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
  rename1 `_ = (sres, es0)` >> Cases_on `sres`
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all lower_vyper_runtime_unit_body_joint >> strip_tac >>
      simp[source_unit_execution_correct_def,
           source_unit_execution_correct_at_def] >>
      qexists_tac `marks` >>
      qexistsl_tac [`shadow_ctx`, `func`, `shadow_func`] >> simp[]) >>
  irule external_entry_value_revert >> metis_tac[]
QED
