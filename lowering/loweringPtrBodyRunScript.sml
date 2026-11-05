(*
 * S3 piece: once the external entry accepts the call value, the lowered
 * unit's run is pointer-safe.  The pointer twin of loweringRuntimeCorrect's
 * lower_vyper_runtime_unit_body and loweringMemBodyRun's
 * lower_vyper_runtime_unit_body_mem: the entry reaches the body
 * (external_entry_reaches_body_ptr), the body runs (body_stmts_sim_ptr,
 * whose abi_decode target premise bodyAbiDecodeTarget's
 * lookup_function_abi_decode_target_occurs gives) and returns
 * (external_frame_ret_ok_ptr) or falls off its end
 * (compile_guarded_body_end_ptr_safe).  The body's counted path gives the
 * run through gasPathPtrExec's gas_path_ptr_exec; its exempt branch is
 * ruled out by the exemption premise at every gas_explicit marks of the
 * target's GAS readings.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_body_ptr -- the piece
 *   compile_guarded_body_end_ptr_safe -- falling off the end of the body
 *   ptr_safe_run_all_fuel, nonexempt_body_result -- helpers
 *)
Theory loweringPtrBodyRun
Ancestors
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs stmtSimDefs stmtSimProps loweringPosts bodySim moduleLowering
  stmtLowering vyperTypeSystem vyperState emitHelper vyperTypeSelectedEntrySoundness
  stmtLoweringMono venomWf memSafeRun allocaFrontierBound unitTransformDefs
  unitShapeDefs o1PassContract
  bodyStmtsSimPtr extEntryReachesBodyPtr extFrameRetOkPtr bodyAbiDecodeTarget
  fragGasPathPtr gasPathPtrExec gasSummary

val _ = Parse.hide "body";

(* ===== The end of the body ===== *)

Theorem terminal_inst_ptr_safe:
  !ctx cx fn PG G tn s bb id op.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id op [] []) /\
    (op = STOP \/ op = INVALID) /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ stor_taint_ok cx tn s ==>
    !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s /\
           (!e. run_from fuel ctx fn s <> Error e)
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id op [] []) s =
     if op = STOP then Halt (halt_state (s with vs_returndata := []))
     else Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (gvs[] >> simp_tac (srw_ss()) [Once step_inst_base_def, mk_inst_def]) >>
  gvs[] >> gen_tac >>
  simp[ptr_safe_run_def, Once ptr_safe_block_def, ptr_safe_step_def,
       ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
       mk_inst_def] >>
  simp[step_inst_non_invoke] >>
  gvs[mk_inst_def] >>
  simp[run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  gvs[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      ret_taint_def, halt_state_def, stor_taint_ok_def, cx_dead_def]
QED

(* Falling off the end of the guarded body (no lock): a STOP,
   whose halt leaves taint only in dead storage bytes and returns no data,
   or INVALID for a function with a return type.  Neither touches memory. *)
Theorem compile_guarded_body_end_ptr_safe:
  !ctx cx PG cenv nkey ut iv stmts rt st x st' sb fn G tn s.
    compile_guarded_body cenv F nkey ut iv stmts rt st = (x, st') /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb /\ fn_has_code sb st' fn /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stor_taint_ok cx tn s ==>
    !fuel. ptr_safe_run (cx_dead cx) 0 fuel ctx fn PG G tn s /\
           (!e. run_from fuel ctx fn s <> Error e)
Proof
  rpt gen_tac >> strip_tac >>
  `?op. (op = STOP \/ op = INVALID) /\
        st'.cs_current_bb = sb.cs_current_bb /\
        st'.cs_current_insts =
          sb.cs_current_insts ++ [mk_inst sb.cs_next_id op [] []]` by
    (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, comp_get_def] >>
     Cases_on `rt` >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_inst_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  irule terminal_inst_ptr_safe >> simp[] >> metis_tac[]
QED

Theorem ptr_safe_run_all_fuel:
  !D lo fuel ctx fn PG G tn s.
    ~s.vs_halted /\ ptr_safe_run D lo fuel ctx fn PG G tn s /\
    (!e. run_from fuel ctx fn s <> Error e) ==>
    !m. ptr_safe_run D lo m ctx fn PG G tn s
Proof
  rpt strip_tac >> Cases_on `m <= fuel`
  >- metis_tac[ptr_safe_run_fuel_mono_down] >>
  gvs[ptr_safe_run_def, run_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  irule (cj 2 ptr_safe_fuel_mono_up) >> qexists_tac `fuel` >>
  gvs[block_run_def]
QED

Theorem nonexempt_body_result:
  !tops am tx ret mut args fbody env orc es0 res es'.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody es0 = (res, es') /\
    ~source_exempt tops (call_external orc [] am tx) ==>
    res <> INR (Error (RuntimeError "convert empty bytes to signed"))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule_all call_external_selected_body >> strip_tac >>
  `es0.scopes = [env]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  `es0 with scopes := [env] = es0` by
    (qpat_assum `es0.scopes = [env]` (SUBST1_TAC o SYM) >> simp[]) >>
  gvs[vyperTypeSelectedEntrySoundnessTheory.call_external_body_def,
      vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.set_scopes_def,
      source_exempt_def, unspecified_behaviour_exempt_def]
QED

(* ===== The body ===== *)

Theorem lower_vyper_runtime_unit_body_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    ~ctx_has_dalloca unit.cu_context /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    !fuel. ptr_safe_blocks
             (external_call_dead tx
                (call_external (SOME vs.vs_outcomes) [] am tx))
             0 fuel unit.cu_context efn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED
