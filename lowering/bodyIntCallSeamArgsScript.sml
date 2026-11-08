(* Seam 1 of the internal call: the caller's code up to the INVOKE. *)

Theory bodyIntCallSeamArgs
Ancestors
  bodyIntCallSeamDefs
  bodyIntCallJointContract
  bodyIntCallSource bodyIntCallWidenedPost bodyIntCallWidenedEndpoint
  bodyIntCallSourceReturn bodyIntCallMetadata bodyIntCallReturnAdapters bodyIntCallCompilerBoundary bodyIntCallAssemblySource bodyIntCallAssemblyModes bodyIntCallAssembly bodyIntCallCompletedModes bodyIntCallCompletedFrame bodyIntCallCompletedFacts bodyIntCallCompletedSource bodyIntCallExemptReturn bodyIntCallStorePath bodyIntCallStoreRun bodyIntCallStorePost bodyIntCallEmitBoundary memoryLocalRhsProps supportedProgram supportedNames bodyIntCallReturnLayout bodyIntCallRestoreResults bodyIntCallRestoreFrame bodyIntCallCallerFrame bodyIntCallCountedPath bodyIntCallReturnBoundaryChecks bodyIntCallImmutableFrame bodyIntCallReturnSource bodySim exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  intCallCallee intCallFrame fragGasFocus gasOutcome gasContext
  bodyIntCallAllocatedForcing bodyIntCallAggregateStoreFrame bodyIntCallAggregateStoreLanding bodyIntCallSubslotGeometry bodyIntCallForcing bodyIntCallForcingCode bodyIntCallForcingCodeRun bodyIntCallForcingStorage bodyIntCallForcingReadOnly bodyIntCallStorageLanding bodyIntCallMaterializeLanding bodyIntCallSharpReturn bodyIntCallParameterGeometry bodyIntCallSourceSpans bodyIntCallStageOrigin bodyIntCallCopySharpRank bodyIntCallCopySharpDynamic bodyIntCallCopySharpFixed bodyIntCallCopySharpFast bodyIntCallCopySharpFields bodyIntCallCopySharpArray bodyIntCallCopySharpPrimitive bodyIntCallWidenCopy bodyIntCallDeclarationStore bodyIntCallDeclarationAlloc bodyIntCallDeclarationRegions bodyIntCallPrologueInit bodyIntCallLocalLanding bodyIntCallNameLanding bodyIntCallForceLanding bodyIntCallWordLanding bodyIntCallLiteralLanding bodyIntCallBodyTyping bodyIntCallSemanticEntry bodyIntCallHandler bodyIntCallResourceExit bodyIntCallPrologueResource bodyIntCallFrameProbe bodyIntCallReturnProbe bodyIntCallReturnCopy bodyIntCallProtectedLiteral bodyIntCallProtectedAlloc bodyIntCallProtectedBuffer bodyIntCallProtectedBytelike
  bodyIntCallWriteAuthorization bodyIntCallResourceEntry bodyIntCallResourceSpans bodyIntCallNormalResource bodyIntCallOutcomeFrame bodyIntCallFrameBoundary bodyIntCallReturnBoundary bodyIntCallReachableReturn bodyIntCallProducerOrder bodyIntCallProtectedReturn
  compileVyper exprLowering exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperAST venomState venomExecSemantics
Libs
  monadsyntax

(* Seam 1: argument evaluation and the callee's frame setup.  The
   caller's code up to the INVOKE runs against the source up to
   push_function, so any continuation from an intcall_entry state gives
   the whole call. *)
Theorem intcall_args_frame_setup:
  !tops ctx func cenv cx tenv ty ann name es dflt es0 sa sb vv s0
   mut args ret ss rr Q R.
    body_inv tops ctx cenv cx /\
    cenv_module_pins tops cenv /\
    expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
    lookup_callable_function cx.in_deploy name tops =
      SOME (mut,F,args,[],ret,ss) /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops /\
    (~MEM (NONE,name) cx.stk ==> body_results_ok cx es) /\
    compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt) sa =
      (vv,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt))
      expr_vv_res_ok es0 /\
    stmt_state_rel ctx func cenv cx es0 s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!res ee r. expr_exit res r ==> R res ee r) /\
    (!prev penv rtv es1 t.
       intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
         (mut,args,ret,ss,rr) prev penv rtv es1 t ==>
       gas_outcome F (cx_tops cx) (ctx,func) (intcall_rest cx name mut ss prev rtv)
         (es1,t) Q R) ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (eval_expr cx (Call ann (IntCall (NONE,name)) es dflt)) (es0,s0) Q R
Proof
  cheat
QED
