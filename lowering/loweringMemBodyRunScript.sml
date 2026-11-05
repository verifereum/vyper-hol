(*
 * S3 piece: once the external entry accepts the call value, the lowered
 * unit's run is memory-safe.  The memory twin of loweringRuntimeCorrect's
 * lower_vyper_runtime_unit_body: the entry reaches the body
 * (external_entry_reaches_body_mem), the body runs (bodyMemory's
 * body_stmts_sim_mem) and returns (external_frame_ret_ok_mem) or falls off
 * its end (compile_guarded_body_end_mem_safe).  bodyMemory joins the
 * ancestors with the composition's proof, once bodyMemory's own cone
 * builds after the GAS join; its body_stmts_sim_mem's abi_decode target
 * premise holds for the called body by bodyAbiDecodeTarget's
 * lookup_function_abi_decode_target_occurs.
 *)
Theory loweringMemBodyRun
Ancestors
  stmtSimDefs
  loweringPosts
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect loweringRuntimeCorrect fragExecMem bodyMemoryDefs
  entryHaltMem loweringPtrCorrect bodySim bodySimMain moduleLowering
  stmtLowering vyperTypeSystem vyperState lowerDloadDefs
  bodyAbiDecodeTarget loweringMemEntryReach loweringMemFrameRet

val _ = Parse.hide "body";

(* ===== The end of the body ===== *)

(* Falling off the end of the guarded body (no lock): a STOP, or INVALID
   for a function with a return type; neither touches memory. *)
Theorem compile_guarded_body_end_mem_safe:
  !ctx cenv nkey ut iv stmts rt st x st' sb fn s.
    compile_guarded_body cenv F nkey ut iv stmts rt st = (x, st') /\
    compile_stmts cenv NoLoop
      (case rt of SOME t => t | NONE => BaseT BoolT) stmts st = ((), sb) /\
    ~block_is_terminated sb /\ fn_has_code sb st' fn /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    !fuel. mem_safe_run fuel ctx fn s /\ (!e. run_from fuel ctx fn s <> Error e)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `rt` >>
  gvs[compile_guarded_body_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, comp_get_def, emitHelperTheory.emit_inst_def,
      fresh_id_def, emit_def] >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts ++ [inst]` >>
  drule fn_has_code_same_block >> simp[] >>
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by simp[] >>
  gen_tac >>
  `mem_safe_step fuel ctx inst s` by
    simp[Abbr `inst`, mem_safe_step_non_invoke,
         inst_mem_below_frontier_def, source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
  `?r. step_inst fuel ctx inst s = r /\
       (!s'. r <> OK s') /\ (!e. r <> Error e)` by
    (simp[Abbr `inst`, step_inst_non_invoke] >>
     pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all run_from_step_exit >> simp[]
QED

(* The source exemption rules out the body judgment's exceptional error. *)
Theorem external_body_not_empty_bytes_error:
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
      vyperStateTheory.return_def, vyperStateTheory.set_scopes_def, source_exempt_def,
      unspecified_behaviour_exempt_def]
QED

(* ADMITTED: the composition, still to be ported to the counted (GAS)
   stmt_frag_mem.  Its fixed-run proof, with the fixed-run
   stmt_frag_mem_complete it used, is lower_vyper_runtime_unit_run_mem_safe's
   INL case in loweringMemCorrectScript.sml at 18f70e04a. *)
Theorem lower_vyper_runtime_unit_body_mem:
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
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    !fuel. mem_safe_blocks fuel unit.cu_context efn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                         vs_inst_idx := 0 |>)
Proof
  cheat
QED
