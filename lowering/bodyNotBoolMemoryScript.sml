(* Memory-checked not on a bool operand. *)
Theory bodyNotBoolMemory
Ancestors
  bodyUnopFragMemory exprSimMemoryStack exprSimMemDefs exprSimSource
  exprSimUnopProps exprSimUnopCompose exprLoweringProps freshWrites
  exprLowering compileEnv vyperContext vyperTypeSystem vyperTyping vyperValue
  vyperAST vyperInterpreter

Theorem compile_not_bool_sim_mem:
  expr_type e = BaseT BoolT /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (BaseT BoolT) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (BaseT BoolT) Not [e]) es
Proof
  strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `ty`, `e`, `es`]
    mp_tac compile_not_sim_mem >>
  gvs[]
QED

Theorem compile_not_bool_vv_sim_mem:
  expr_type e = BaseT BoolT /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (BaseT BoolT) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT BoolT) Not [e]) es
Proof
  strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `ty`, `e`, `es`]
    mp_tac compile_not_vv_sim_mem >>
  gvs[]
QED
