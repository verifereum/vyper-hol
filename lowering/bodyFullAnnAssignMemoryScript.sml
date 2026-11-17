(* Joint ordinary-memory and empty AnnAssign execution. *)
Theory bodyFullAnnAssignMemory
Ancestors
  bodyFullPreds bodySimFull bodyInvNoDalloca gasShadow
  bodySimDeclCases bodyExprPreFacts exprSimHyps exprSimHypsDefs exprSimSource
  memoryLocalRhsProps supportedStmts supportedStmtTraverse
  stmtSimDeclEmpty stmtSimDeclSource bodyDeclCopyMemory
  gasShadowCompileStmtHelpers gasShadowCompileStmtBase
  bodyFullAllocaFresh bodyFullMemoryStore
  compileEnv exprLowering stmtLowering loweringPosts
  vyperTypeSystem vyperTypeArgFits vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

(* The physical source footprint is positive and fits in the destination;
   its runtime type is not identified with the destination runtime type. *)
Theorem annassign_memory_full_source_layout[local]:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) typ /\
  (expr_type e = typ \/ is_bytestring_type typ) /\
  0 < type_memory_bytes ce typ /\ type_memory_bytes ce typ < 2 ** 64 /\
  (lowered_value_type ce e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    0 < type_memory_size stv /\
    type_memory_size stv <= type_memory_bytes ce typ
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `0 < type_memory_bytes ce (lowered_value_type ce e) /\
   type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce typ` by
    metis_tac[memory_rhs_destination_bound] >>
  `type_memory_bytes ce (lowered_value_type ce e) < 2 ** 64` by decide_tac >>
  drule_all memory_rhs_lowered_runtime_layout >> strip_tac >>
  qexists_tac `ltv` >> gvs[]
QED
