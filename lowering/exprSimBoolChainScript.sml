(*
 * Expression simulation: an and/or chain (BoolChain)
 *
 * The frontend wraps the nested conditional it builds for an and/or chain
 * of three or more operands in the identity builtin BoolChain, and the
 * lowering compiles the operands read back by bool_chain_operands with
 * compile_bool_chain_ops, as the pinned compiler's lower_BoolOp does: each
 * operand but the last tested in turn with a jump to a block that sets the
 * result and leaves, the last one's value the result.
 *
 * The case lemma takes the operands' judgments in the style of
 * compile_ifexp_case (exprSimOperators): each later operand's where the
 * earlier one evaluates, as the body predicates' conditional clause gives
 * them.
 *
 * TOP-LEVEL:
 *   bool_chain_case_def      - the operands' judgments, in order
 *   compile_bool_chain_case  - the chain's judgments from its operands'
 *)
Theory exprSimBoolChain
Ancestors
  exprSimIfExp exprSimOperators exprSimProps exprSimDefs exprSimHypsDefs
  exprLowering

(* Each operand simulates, a later one where the one before evaluates. *)
Definition bool_chain_case_def:
  bool_chain_case nocalls ctx func cenv cx [] = T /\
  bool_chain_case nocalls ctx func cenv cx (e::es) =
    (expr_sim_case nocalls ctx func cenv cx e /\
     expr_vv_case nocalls ctx func cenv cx e /\
     ((?s tv s'. eval_expr cx e s = (INL tv, s')) ==>
      bool_chain_case nocalls ctx func cenv cx es))
End

(* The chain is the identity on its one argument, the nested conditional;
   its code tests the operands in turn (compile_bool_chain_ops), which
   computes the conditional's value: an and stops at the first false
   operand with false, an or at the first true one with true. *)
Theorem compile_bool_chain_case:
  !nocalls ctx func cenv cx ann is_and n e.
    bool_chain_case nocalls ctx func cenv cx
      (bool_chain_operands is_and (n - 1) e) ==>
    expr_sim_case nocalls ctx func cenv cx
      (Builtin ann (BoolChain is_and n) [e]) /\
    expr_vv_case nocalls ctx func cenv cx
      (Builtin ann (BoolChain is_and n) [e])
Proof
  cheat
QED
