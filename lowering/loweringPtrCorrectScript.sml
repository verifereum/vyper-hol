(*
 * S3, Milestone 5: the lowered unit's raw run is pointer-safe
 *
 * lower_vyper_runtime_unit_run_ptr_safe_composed is composed as S1 is
 * (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct): the entry
 * reaches the selected function's body or reverts on the call value, the
 * body runs, and it returns or falls off its end.  Each piece is the
 * pointer-safe twin of S1's, by bodyPtrDefs's judgments at d = NONE (an
 * external frame has no caller return buffer) and PG = [] (__entry has no
 * parameters).  loweringMemCorrect's lower_vyper_runtime_unit_ptr_taint
 * takes S3's pointer discipline and taint bound from it.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_run_ptr_safe_composed -- the pointer-safe run
 *   compile_guarded_body_end_ptr_safe -- falling off the end of the body
 *
 * Named admissions (cheats), each a pointer twin of a piece S1 rests on:
 *   body_stmts_sim_ptr -- body_stmts_sim with the ghost
 *   external_entry_value_revert_ptr, external_entry_reaches_body_ptr --
 *     S1's entry bridge with the ghost
 *   external_frame_ret_ok_ptr -- the frame's returns with the ghost
 *
 * Inherited admissions: the composition also uses S1's
 * external_body_frame, external_body_source_ok and stmts_env_ret_ty
 * (loweringRuntimeCorrect).
 *)
Theory loweringPtrCorrect
Ancestors calldataScratchLoopPtr calldataScratchArrayPtr decoderScratchInitPtr calldataScratchTuplePtr calldataScratchBytesPtr calldataScratchWordPtr decoderArrayInitPtr decoderAllocationBoundsPtr decoderArraySetupPtr decoderScratchLoopPtr decoderLoopControlPtr decoderProtectedScratchPtr decoderIndexInitPtr calldataValidWordInputPtr typedCopyArrayExecutionPtr batchCopyRobustPtr normalizationAllocPtr typedCopyLoopBackedgePtr
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs stmtSim bodySim moduleLowering
  stmtLowering vyperTypeSystem vyperState emitHelper vyperTypeSelectedEntrySoundness
  fragExecPtr typedCopyFieldsPtr typedCopyBytesRobustPtr
  typedCopyOffsetPtr typedCopyBytesFieldsPtr typedCopyTuplePtr
  robustCopyTransportPtr staticTypeFitsPtr liveArrayTransportPtr structChildPtr
  wordCopyRobustPtr
  stmtLoweringMono venomWf memSafeRun allocaFrontierBound unitTransformDefs
  unitShapeDefs o1PassContract rawEntryCode entryChecksPtr sourceValueRejection entryCheckIntervals sourceEntrySelection entryDispatchPtr sourceEntryCode entryValueRevertPtr
  loweringShapeProps loweringShapeSource supportedNames supportedDecls
  entryDispatchProps o1PipelineCorrect selectedBodyCode calldataDecodePtr calldataTypedRobustPtr

val _ = Parse.hide "body";

(* ===== The body ===== *)

(* ADMITTED: body_stmts_sim with the ghost, in a frame whose caller return
   buffer, if any, is d, and whose parameters' provenance is PG. *)
Theorem body_stmts_sim_ptr:
  !d tops bindings ctx PG func cenv cx env env' ret_ty lctx RetQ ss es res
   es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    eval_stmts cx ss es = (res, es') ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) es res es'
Proof
  cheat
QED

(* ===== The entry ===== *)

(* The raw lowering boundary rejects policies outside its frontend contract. *)
Theorem run_lowering_policy_ok:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info entry_label = SOME unit ==>
  lowering_policy_ok rpolicy
Proof
  Cases_on `lowering_policy_ok rpolicy` >> simp[run_lowering_def]
QED

(* Value rejection follows the installed dispatcher into the nonpayable check. *)
Theorem external_entry_value_revert_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env e st efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    !fuel. ptr_safe_blocks
             (external_call_dead tx
                (call_external (SOME vs.vs_outcomes) [] am tx))
             0 fuel unit.cu_context efn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_storage_ok _ _ _` kall_tac >>
  qpat_x_assum `source_deployment_rel _ _ _` kall_tac >>
  qpat_x_assum `call_outcomes_ok _ _ _` kall_tac >>
  qpat_x_assum `~source_exempt _ _` kall_tac >>
  `tx.function_name <> "__default__"` by fs[valid_vyper_call_def] >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule o1_source_unit_ok_no_dalloca >>
     irule loweringShapePropsTheory.lower_vyper_runtime_unit_source_unit_ok_shape >>
     goal_assum (drule_at Any) >> conj_tac
     >- (irule supported_names_internal_names_distinct >>
         fs[supported_program_def, supported_declaration_names_def]) >>
     metis_tac[supported_program_runtime_bodies_shape_ok]) >>
  drule_all initial_entry_rejected_value >> strip_tac >>
  drule_all source_valid_linear_dispatch_target >> strip_tac >>
  drule_all source_selected_entry_check_code >> strip_tac >>
  drule_all initial_entry_dispatch_scalars >>
  disch_then (qspecl_then [`0`, `elbl`, `ds`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `ptr_safe_blocks D 0 _ _ _ _ _ _ ss` >>
  `!G tn fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G tn ss` by
    (irule dispatch_nonpayable_check_ptr_safe >>
     simp[Abbr `ss`] >>
     qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
       `MAP (\(sel,lbl,z). (sel,lbl))
          (build_selectors (type_env tops) (FST (classify_functions tops)))`,
       `ds`, `de`] >>
     gvs[] >>
     qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
       mp_tac linear_selectors_lt >> simp[]) >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  irule ptr_safe_blocks_nonphi_run >>
  simp[Abbr `ss`] >>
  qexistsl_tac [`b0`, `mk_inst ds.cs_next_id CALLDATASIZE []
    [STRING #"%" (toString ds.cs_next_var)]`] >>
  gvs[mk_inst_def]
QED

(* ADMITTED: external_entry_reaches_body, with the body's frame free of a
   caller return buffer, the ghost at the body's start in ghost_inv, and a
   pointer-safe run from the body's start (from that ghost) making the run
   from __entry pointer-safe: the selector dispatch and the entry checks
   touch no memory, and the argument decode writes only the parameters'
   buffers, untainted. *)
Theorem external_entry_reaches_body_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0 G0 tn0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      stmt_state_rel unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      ghost_inv NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0
        G0 tn0 s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      cenv.ce_return_buf = NONE /\
      ((!fuel. ptr_safe_run
                 (cx_dead
                    (initial_evaluation_context am.sources am.layouts tx
                       NONE))
                 0 fuel unit.cu_context func [] G0 tn0 s0) ==>
       !fuel. ptr_safe_blocks
                (external_call_dead tx
                   (call_external (SOME vs.vs_outcomes) [] am tx))
                0 fuel unit.cu_context efn [] FEMPTY entry_taint
                (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                            vs_inst_idx := 0 |>))
Proof
  cheat
QED

(* ===== The frame's returns ===== *)

(* ADMITTED: external_frame_ret_ok with the ghost, for any outcome of the
   return: every return sequence halts pointer-safely, its return data
   untainted. *)
Theorem external_frame_ret_ok_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok_ptr NONE unit.cu_context [] func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\v es gt r. T) cenv ret
Proof
  cheat
QED

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
  >- (drule_all ptr_safe_run_fuel_mono_down >> simp[]) >>
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

(* ===== S3 ===== *)

(* The composition.  The
   source call's dead bytes are cx_dead of the call's context; no DALLOCA
   is the judgments' ~ctx_has_dalloca. *)
Theorem lower_vyper_runtime_unit_run_ptr_safe_composed:
  !tops rpolicy unit am tx ret vs fn lbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    ~ctx_has_dalloca unit.cu_context /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    !fuel. ptr_safe_blocks
             (external_call_dead tx
                (call_external (SOME vs.vs_outcomes) [] am tx))
             0 fuel unit.cu_context fn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  `?mut args fbody.
     lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody) /\
     LENGTH tx.args = LENGTH args /\
     IS_SOME (bind_arguments (type_env tops) args tx.args)` by
    (fs[valid_vyper_call_def] >> metis_tac[]) >>
  `?env. bind_arguments (type_env tops) args tx.args = SOME env` by
    (Cases_on `bind_arguments (type_env tops) args tx.args` >> fs[]) >>
  Cases_on `send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
        <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sent, es0)` >> Cases_on `sent`
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all external_entry_reaches_body_ptr >> strip_tac >>
      first_x_assum irule >>
      drule_all external_body_frame >> strip_tac >>
      drule_all external_frame_ret_ok_ptr >>
      disch_then (qspec_then `func` assume_tac) >>
      Cases_on `eval_stmts
        (initial_evaluation_context am.sources am.layouts tx NONE)
        fbody es0` >> rename1 `_ = (res, es')` >>
      drule_all external_body_source_ok >> strip_tac >>
      drule_all nonexempt_body_result >> strip_tac >>
      qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
      `rt = if ret = NoneT then NONE else SOME ret` by
        gvs[package_external_fn_def, set_external_package_target_def] >>
      `?sb. compile_stmts cenv NoLoop
          (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa = ((), sb) /\
          cs_extends sa sb /\ cs_extends sb st'` by
        (qpat_x_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` mp_tac >>
         simp[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
              comp_get_def, comp_return_def] >>
         Cases_on `compile_stmts cenv NoLoop
           (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa` >>
         rename1 `_ = (u, sb)` >> Cases_on `u` >> simp[] >>
         `cs_extends sa sb` by
           (qspecl_then [`cenv`, `NoLoop`,
             `case rt of SOME t => t | NONE => BaseT BoolT`, `fbody`]
             mp_tac (cj 2 compile_stmt_cs_mono) >>
            simp[cs_mono_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
         rw[] >>
         gvs[comp_return_def, comp_ignore_bind_def, comp_bind_def,
             cs_extends_refl] >>
         drule (SIMP_RULE std_ss [cs_appends_def]
           (cj 1 cs_appends_emit_helpers)) >> simp[]) >>
      `?cenv'. stmts_env cenv NoLoop ret fbody sa = (cenv', sb)` by
        (`stmts_env cenv NoLoop ret fbody sa =
          stmts_env cenv NoLoop
            (case rt of SOME t => t | NONE => BaseT BoolT) fbody sa` by
           (Cases_on `ret = NoneT` >> gvs[] >>
            drule type_stmts_none_valued_return >> strip_tac >>
            drule_all stmts_env_ret_ty >>
            disch_then (qspecl_then [`NoLoop`, `NoneT`, `BaseT BoolT`]
              SUBST1_TAC) >> simp[]) >>
         gvs[compile_stmts_env] >>
         metis_tac[pairTheory.PAIR]) >>
      `fn_has_code sa sb func /\ fn_has_code sb st' func` by
        (drule_all fn_has_code_split >> simp[]) >>
      `stmt_frag_ptr NONE unit.cu_context [] func cx NoLoop
         (\v es gt r. T) cenv (stmts_env cenv NoLoop ret fbody) es0 res es'` by
        (irule body_stmts_sim_ptr >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
      qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[stmt_frag_ptr_def] >>
      disch_then (qspecl_then [`sa`, `sb`, `s0`, `G0`, `tn0`, `cenv'`] mp_tac) >>
      impl_tac >- gvs[ret_pc_ok_def] >>
      map_every (fn pat => rpt (qpat_x_assum pat kall_tac))
        [`lower_vyper_runtime_unit _ _ = _`, `supported_program _`,
         `source_typing_ok _ _ _`, `source_storage_ok _ _ _`,
         `source_deployment_rel _ _ _`, `valid_vyper_call _ _ _ _`,
         `initial_venom_state_rel _ _ _ _`, `call_outcomes_ok _ _ _`,
         `~source_exempt _ _`, `lookup_function _ _ = _`,
         `lookup_function _ _ _ _ _ = _`, `fn_entry_label _ = _`,
         `LENGTH _ = LENGTH _`, `IS_SOME _`, `bind_arguments _ _ _ = _`,
         `send_call_value _ _ _ = _`, `set_external_package_target _ _ = _`,
         `compile_register_positional_args _ _ _ _ = _`,
         `body_inv _ _ _ _`, `supported_stmts _ _ _`,
         `expr_sim_inv _ _ _ _ _`, `ce_locals_declared _ _`,
         `locals_alloc_ok _ _`, `type_stmts _ _ _ = _`,
         `EVERY _ _`, `call_evaluation_safe _ _`,
         `frame_ret_ok_ptr _ _ _ _ _ _ _ _`, `eval_stmts _ _ _ = _`,
         `call_external _ _ _ _ = _`] >>
      strip_tac
      >- (gvs[stmt_lands_def] >>
          `stor_taint_ok cx tn s` by fs[ghost_inv_def] >>
          `ptr_safe_run (cx_dead cx) 0 0 unit.cu_context func [] G tn s /\
           (!e. run_from 0 unit.cu_context func s <> Error e)` by
            (irule compile_guarded_body_end_ptr_safe >>
             qpat_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _`
               (irule_at Any) >>
             qexists_tac `sb` >> simp[]) >>
          first_x_assum (qspec_then `0` mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          irule ptr_safe_run_all_fuel >> goal_assum (drule_at Any) >>
          simp[] >> metis_tac[]) >>
      irule ptr_safe_run_all_fuel >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[exit_result_not_error]) >>
  drule_all external_entry_value_revert_ptr >> simp[]
QED
