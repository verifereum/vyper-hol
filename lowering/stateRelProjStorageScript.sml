Theory stateRelProjStorage
Ancestors
  loweringStateRelDefs exprLoweringProps vyperTypeSystem supportedStmts

Theorem state_rel_storage_rel:
  state_rel H func cenv cx vs ss ==> storage_rel H cx.txn.target vs ss
Proof
  simp[loweringStateRelDefsTheory.state_rel_def]
QED

Theorem state_rel_transient_rel:
  state_rel H func cenv cx vs ss ==> transient_rel H cx.txn.target vs ss
Proof
  simp[loweringStateRelDefsTheory.state_rel_def]
QED
