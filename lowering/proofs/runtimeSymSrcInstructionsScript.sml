Theory runtimeSymSrcInstructions
Ancestors
  runtimeSymSrcPrimitives runtimeSymSrcExpressions runtimeSymSrcStatements
  runtimeSymSrcRuntimeBoundary runtimeSymSrcDynarrayAppend runtimeSymSrcAbiEncode

Theorem runtime_sym_expr_closed:
  !tops ce ty e. runtime_sym_expr_contract tops compile_expr ce ty e
Proof
  metis_tac[runtime_sym_expression_contracts, runtime_sym_generators]
QED

