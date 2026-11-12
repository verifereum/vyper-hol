Theory bodyPtrStructLitOwnershipDeclarationRoute
Ancestors bodyPtrStructLitOwnershipEnvironment bodyPtrStructLitOwnershipReservation
  bodyPtrStructLitCompilerOwnership bodyPtrStructLitOwnershipSteps
  loweringShapeDefs stmtLowering compileEnv

Theorem declare_stmt_local_annassign_commit:
  ce.ce_alloca_locals /\ shape_base_state st /\ alloc_writers_unique st /\
  declare_stmt_local ce (AnnAssign id ty e) st = (ce',st1) /\
  emit_local_alloca ce' id st1 = (u,st2) ==>
  alloc_writers_unique st2 /\ alloc_frame st st2 /\ ce'.ce_alloca_locals
Proof
  simp[declare_stmt_local_def] >> strip_tac >>
  drule declare_local_alloca_mode >> strip_tac >>
  drule_all declare_local_alloca_fresh_commit >> simp[]
QED

Theorem declare_stmt_local_nonannassign_identity:
  (!id ty e. s <> AnnAssign id ty e) /\
  declare_stmt_local ce s st = (ce',st1) ==> ce' = ce /\ st1 = st
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def] >>
  metis_tac[]
QED
