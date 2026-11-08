(*
 * S3, Milestone 5: the lowered unit's raw run is pointer-safe
 *
 * lower_vyper_runtime_unit_run_ptr_safe_composed is composed as S1 is
 * (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct): the entry
 * reverts on the call value, or accepts it and the body's run is
 * pointer-safe.  Each piece is the pointer-safe twin of S1's, by
 * bodyPtrDefs's judgments at d = NONE (an external frame has no caller
 * return buffer) and PG = [] (__entry has no parameters).  The source
 * exemption is excluded at every gas_explicit marks of the target's GAS
 * readings, as S1 indexes it: at [] alone, a body reading msg.gas stops
 * with "no gas reading" in the source while the target runs on.
 * loweringMemCorrect's lower_vyper_runtime_unit_ptr_taint takes S3's
 * pointer discipline and taint bound from it.
 *
 * TOP-LEVEL:
 *   lower_vyper_runtime_unit_run_ptr_safe_composed -- the pointer-safe run
 *
 * The pieces, each in its own leaf theory:
 *   external_entry_value_revert_ptr (extEntryValueRevertPtr) -- the entry
 *     reverting on the call value
 *   lower_vyper_runtime_unit_body_ptr (loweringPtrBodyRun) -- the entry
 *     accepting it and the body running, from:
 *     body_stmts_sim_ptr (bodyStmtsSimPtr, proved from bodySimPtrMain's
 *       body induction, whose cases are pieces),
 *     external_entry_reaches_body_ptr (extEntryReachesBodyPtr),
 *     external_frame_ret_ok_ptr (extFrameRetOkPtr),
 *     gas_path_ptr_exec (gasPathPtrExec) -- a counted path's run
 * *)
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
  loweringPtrBodyRun extEntryValueRevertPtr gasSummary
  calldataScratchArrayConstructorPtr
  calldataScratchArrayEntryPtr calldataScratchArrayCompletePtr
  calldataScratchLoopPtr calldataScratchArrayPtr decoderScratchInitPtr
  calldataScratchTuplePtr calldataScratchBytesPtr calldataScratchWordPtr
  decoderArrayInitPtr decoderAllocationBoundsPtr decoderArraySetupPtr
  decoderScratchLoopPtr decoderLoopControlPtr decoderProtectedScratchPtr
  decoderIndexInitPtr
  normalizationAllocPtr
  fragExecPtr typedCopyFieldsPtr typedCopyBytesRobustPtr typedCopyOffsetPtr
  typedCopyBytesFieldsPtr typedCopyTuplePtr robustCopyTransportPtr
  structChildPtr wordCopyRobustPtr
  rawEntryCode entryChecksPtr sourceValueRejection entryCheckIntervals
  sourceEntrySelection entryDispatchPtr sourceEntryCode entryValueRevertPtr
  loweringShapeProps loweringShapeSource supportedNames supportedDecls
  entryDispatchProps o1PipelineCorrect selectedBodyCode calldataDecodePtr
  calldataTypedRobustPtr entryPtrSeamDead
  entryPtrSeamPrefix entryPtrSeamRegister

val _ = Parse.hide "body";

(* ===== S3 ===== *)

(* The composition.  The source call's dead bytes are cx_dead of the
   call's context; no DALLOCA is the judgments' ~ctx_has_dalloca. *)
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
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
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
  `~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)` by
    metis_tac[gasSummaryTheory.gas_explicit_nil] >>
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
      irule lower_vyper_runtime_unit_body_ptr >> metis_tac[]) >>
  drule_all external_entry_value_revert_ptr >> simp[]
QED
