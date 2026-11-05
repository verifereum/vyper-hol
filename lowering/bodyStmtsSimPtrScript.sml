(*
 * The pointer twin of S1's body_stmts_sim, admitted: the piece the body of
 * loweringPtrCorrect's composition rests on.
 *
 * TOP-LEVEL:
 *   body_stmts_sim_ptr
 *)
Theory bodyStmtsSimPtr
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
