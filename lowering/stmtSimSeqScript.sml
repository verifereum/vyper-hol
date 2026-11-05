(* Statement-list sequencing with the environment-independent tail guard. *)
Theory stmtSimSeq
Ancestors
  stmtSimDefs stmtSimSeqEnv stmtLowering vyperInterpreter vyperState

Theorem stmt_frag_cons:
  !ctx func cx lctx RetQ cenv ty stmt ss es.
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
      (eval_stmt cx stmt) es /\
    (!gs es1 c.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss)) (eval_stmts cx (stmt::ss)) es
Proof
  rpt strip_tac >> irule stmt_frag_cons_env >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED
