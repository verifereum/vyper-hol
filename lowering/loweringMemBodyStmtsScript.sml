(*
 * S3 piece: the body with memory (#641's body footprint), the memory twin
 * of bodySimMain's body_stmts_sim.
 * loweringMemCorrect composes S3 from this and the other leaves.
 *)
Theory loweringMemBodyStmts
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

val _ = Parse.hide "body";

(* ===== The body (#641) ===== *)

(* ADMITTED (#641): body_stmts_sim with memory, in a frame whose
   caller return buffer, if any, is d. *)
Theorem body_stmts_sim_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (eval_stmts cx ss) es
Proof
  cheat
QED
