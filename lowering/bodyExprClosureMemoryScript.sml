(* Reachability-aligned recursive expression memory closure. *)
Theory bodyExprClosureMemory
Ancestors
  bodyNameMemory
  bodyNotFlagMemory bodyNotBytesMemory bodyNotUintMemory
  bodyAbsMemory bodyNotBoolMemory
  exprSimSource
  bodyMemoryPreds bodyMemoryDefs bodyIfExpMemory exprSimOperators exprSimHyps
  exprLoweringProps vyperInterpreter vyperState
  bodyLiteralMemory bodyLiteralForceMemory bodyAllocMemory bodyFieldMemory vyperTypeCallGraph
  bodyUnopMemory bodyNegMemory bodyCalldataMemory bodyEnvMemory bodyFlagMemberMemory
  vyperTyping vyperValue vyperAST vyperTypeSystem

Theorem body_ifexp_word_mem_case:
  !cx t c a b. is_word_type t /\
    (!s tv s'. eval_expr cx c s = (INL tv,s') ==> body_expr_mem_ok cx a) /\
    (!s tv s'. eval_expr cx c s = (INL tv,s') ==> body_expr_mem_ok cx b) /\
    body_expr_mem_ok cx c ==> body_expr_mem_ok cx (IfExp t c a b)
Proof
  cheat
QED

Theorem body_attribute_name_mem_case:
  !cx ann sid id fld.
    body_expr_mem_ok cx (Attribute ann (Name (StructT sid) id) fld)
Proof
  cheat
QED

Theorem body_not_bool_mem_case:
  !cx ann e. expr_type e = BaseT BoolT /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  cheat
QED

Theorem body_abs_mem_case:
  !cx ann e. body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Abs [e])
Proof
  cheat
QED

Theorem body_not_uint256_mem_case:
  !cx ann e. is_uint256_type (expr_type e) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  cheat
QED

Theorem body_not_bytes32_mem_case:
  !cx ann e. is_bytes32_type (expr_type e) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  cheat
QED

Theorem body_not_flag_mem_case:
  !cx ann e. is_flag_type (expr_type e) /\ body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Not [e])
Proof
  cheat
QED

Theorem body_neg_mem_case:
  !cx ann e. body_expr_mem_ok cx e ==>
    body_expr_mem_ok cx (Builtin ann Neg [e])
Proof
  cheat
QED

