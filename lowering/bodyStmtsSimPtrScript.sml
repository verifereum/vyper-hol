(*
 * The pointer twin of S1's body_stmts_sim: the judgment the body of
 * loweringPtrCorrect's composition rests on, from bodySimPtrMain.
 *
 * TOP-LEVEL:
 *   body_stmts_sim_ptr
 *)
Theory bodyStmtsSimPtr
Ancestors
  bodySimPtrMain
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  loweringRuntimeCorrect bodyPtrDefs stmtSimDefs stmtSimProps loweringPosts bodySim moduleLowering
  stmtLowering vyperTypeSystem vyperState emitHelper vyperTypeSelectedEntrySoundness
  stmtLoweringMono venomWf memSafeRun allocaFrontierBound unitTransformDefs
  unitShapeDefs o1PassContract

val _ = Parse.hide "body";

(* body_stmts_sim with the ghost, in a frame whose caller return buffer,
   if any, is d, and whose parameters' provenance is PG. *)
Theorem body_stmts_sim_ptr:
  !d tops bindings ctx PG func cenv cx env env' ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) (eval_stmts cx ss) es
Proof
  metis_tac[body_stmts_ptr_ok_sim]
QED
