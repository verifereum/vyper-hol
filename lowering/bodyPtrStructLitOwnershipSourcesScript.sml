Theory bodyPtrStructLitOwnershipSources
Ancestors supportedProgram supportedDecls loweringShapeProps compileVyper
  supportedStmtTraverse loweringShapeDefs list pair

Theorem structlit_supported_function_body:
  !tops vis mut nr rr name args defaults ret body.
  supported_program tops /\ (vis = Deploy ==> supported_program_deploy tops) /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops ==>
  ~supported_stmts_expr_exists expr_shape_root body
Proof
  rpt gen_tac >> strip_tac >> Cases_on `vis = Deploy`
  >- (gvs[] >> drule_all supported_program_deploy_function >>
      metis_tac[supported_function_body_shape]) >>
  drule_all supported_program_function >>
  metis_tac[supported_function_body_shape]
QED

