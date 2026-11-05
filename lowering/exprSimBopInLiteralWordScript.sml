(*
 * Expression simulation: in and not in on an array literal of words
 * (#569).  The lowering unrolls it to a comparison with each element
 * (compile_multi_exprs, compile_list_membership_in), so it takes the
 * elements' judgments, not the array's.  An array literal of non-words is
 * held for #742 (exprSimBopHeld).
 *
 * TOP-LEVEL:
 *   compile_bop_in_literal_word_sim — that case
 *)

Theory exprSimBopInLiteralWord
Ancestors
  exprSimUnopCompose
  exprSimBopTyped
  exprSimUnopProps
  exprSimSource
  exprSimHypsDefs
  exprSimDefs
  allocLimits
  list finite_map
  fragExec  exprSimHyps exprSimOps exprSimBinopFrag
  exprSimUnop exprSimCompare
  exprBopLowering exprWordOperand
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  vyperStatePreservation

Theorem compile_bop_in_literal_word_sim:
  !cenv ann bop e1 a t n elems.
    is_word_type (expr_type e1) ==>
    expr_sim_below cenv
      (list_size expr_size [e1; Builtin a (MakeArray t n) elems]) /\
    (bop = In \/ bop = NotIn) ==>
    expr_ok cenv (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  cheat
QED
