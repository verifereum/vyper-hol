(*
 * The pointer twin of S1's external_frame_ret_ok, admitted.
 *
 * TOP-LEVEL:
 *   external_frame_ret_ok_ptr
 *)
Theory extFrameRetOkPtr
Ancestors
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs stmtSimDefs stmtSimProps loweringPosts bodySim moduleLowering
  stmtLowering vyperTypeSystem vyperState emitHelper vyperTypeSelectedEntrySoundness
  stmtLoweringMono venomWf memSafeRun allocaFrontierBound unitTransformDefs
  unitShapeDefs o1PassContract extRetScalarCopyCountedPtr extRetBytesCopyCountedPtr
  extRetBulkCopyCountedPtr extRetWordStmtPtr extRetCopySuffixPtr extRetCopyInputsPtr
  extRetOperandBoundaryPtr extRetDispatchProtectionPtr extRetDispatchResultPtr
  extRetStaticStmtPtr extRetStaticReservedPtr extRetStaticFrameMetadataPtr
  extRetStaticFrameConsumerPtr extRetStaticCapacityPtr extRetStaticBoundedConsumerPtr
  extRetRawValuePtr extRetRawStmtPtr extRetAbiReadCleanPtr extRetAbiReadBoundsPtr
  extRetAbiBytesHeaderPtr extRetAbiBytesCountedPtr extRetAbiStaticCountedPtr
  extRetAbiArrayStaticBodyPtr extRetAbiArrayInitPtr extRetAbiArrayBackedgePtr
  extRetAbiArrayStaticLoopPtr extRetAbiArrayStaticCountedPtr extRetAbiSourceInputPtr
  extRetAbiWrappedSourcePtr extRetAbiSingletonCountedPtr extRetAbiSingletonWrapperPtr

val _ = Parse.hide "body";

(* ADMITTED: external_frame_ret_ok with the ghost, for any outcome of the
   return: every return sequence halts pointer-safely, its return data
   untainted.

   Why it should hold: the frame has no return PC or buffer and no
   nonreentrant lock (supported_program forces nr = F), so the lowered
   Return is the returned expression's code (expr_sim_ptr /
   expr_vv_sim_ptr, given) and then one of compile_external_return's
   branches: STOP; ALLOCA 32, MSTORE, RETURN 32 of an untainted word; a raw
   return of a Bytes value's data; or ALLOCA of the max return size, the
   ABI encoder, RETURN of the encoded length, possibly after a widening
   copy into a fresh buffer.  Fresh ALLOCA bytes start tainted, so the
   point is that the encoder writes every byte it returns, from the value's
   pinned (hence untainted, by ptr_mem_ok) bytes or from literals, and
   returns exactly what it wrote. *)
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
