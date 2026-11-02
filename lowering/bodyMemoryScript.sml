(* Body memory safety at the actual frame entry and continuing landings. *)
Theory bodyMemory
Ancestors
  bodyMemoryDefs stmtMemory stmtControlMemory fragLoopMemory
  allocaHistoryFragment builtinBytesMemory concatMemory
  bodySimMain bodySimStmtCases bodySimDeclCases
  bodySim exprSimHyps stmtLoweringProps exprLoweringProps supportedProgram
  vyperInterpreter vyperTypeSystem vyperState

val _ = Parse.hide "body";

Theorem body_stmts_sim_mem:
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    eval_stmts cx ss es = (res, es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) es res es'
Proof
  cheat
QED
