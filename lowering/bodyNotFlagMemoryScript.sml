(* Memory-checked not on a flag operand: the XOR with the flag mask. *)
Theory bodyNotFlagMemory
Ancestors
  bodyUnopFragMemory exprSimMemoryStack exprSimMemDefs exprSimSource
  exprSimUnopProps exprSimUnopCompose exprLoweringProps freshWrites
  exprLowering compileEnv vyperContext vyperTypeSystem vyperTyping vyperValue
  vyperAST vyperInterpreter

Theorem compile_not_flag_sim_mem:
  is_flag_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `ty`, `e`, `es`]
    mp_tac compile_not_sim_mem >>
  gvs[]
QED

Theorem compile_not_flag_vv_sim_mem:
  is_flag_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `ty`, `e`, `es`]
    mp_tac compile_not_vv_sim_mem >>
  gvs[]
QED
