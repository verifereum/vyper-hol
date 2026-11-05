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
Ancestors
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs stmtSimDefs stmtSimProps loweringPosts bodySim moduleLowering
  stmtLowering vyperTypeSystem vyperState emitHelper vyperTypeSelectedEntrySoundness
  stmtLoweringMono venomWf memSafeRun allocaFrontierBound unitTransformDefs
  unitShapeDefs o1PassContract

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

(* ADMITTED: external_entry_value_revert's run is pointer-safe. *)
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
  cheat
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
  cheat
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
  cheat
QED

Theorem ptr_safe_run_all_fuel:
  !D lo fuel ctx fn PG G tn s.
    ~s.vs_halted /\ ptr_safe_run D lo fuel ctx fn PG G tn s /\
    (!e. run_from fuel ctx fn s <> Error e) ==>
    !m. ptr_safe_run D lo m ctx fn PG G tn s
Proof
  cheat
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
  cheat
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
  cheat
QED
