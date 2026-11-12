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
  externalEntryValueRevert

val _ = Parse.hide "body";

(* ===== The unit's storage guards ===== *)

(* Storage guards that hold of the source call's observations put them in
   their own horizon's domain. *)
Theorem source_storage_guards_domain[local]:
  source_storage_ok am tx os gs /\ call_outcomes_storage_ok am tx os gs ==>
  storage_trace_domain
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) (source_storage_trace am tx os gs)
Proof
  simp[source_storage_ok_def, call_outcomes_storage_ok_def,
       storage_trace_domain_def, valid_horizon_def,
       storage_observations_ok_def, storage_trace_horizon_def,
       listTheory.EVERY_MEM]
QED

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

(* ===== S1 ===== *)

(* S1 when the value moves and the body starts.
   STAGED: composition pending the ENTRY-H-r3 producer, the Return
   producers behind external_frame_ret_ok_full, the H port of the guarded
   body's end, and this task's shadow placement and trace lemmas. *)
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
  cheat
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
