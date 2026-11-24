Theory createSizeOperandPreMods
Ancestors
  createSizeOperandPre createExprSizeExitDefsMods
  exprBodyPreProps exprSimHypsDefs exprSimHyps exprSimSource allocLimits
  supportedExprTraverse vyperAST vyperTypeSystem vyperTypeCallGraph
  vyperTypeEvalProofs vyperTypeCallStackSoundness list

Theorem create_call_operand_body_pre_mods:
  expr_body_pre_mods mods ce cx env (Call ann target args df) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env ee ==>
  expr_body_pre_mods mods ce cx env e ee
Proof
  cheat
QED
