(*
 * Joint body simulation: an and/or chain (BoolChain)
 *
 * The joint (full) twin of exprSimBoolChain's compile_bool_chain_case, as
 * bodyFullIfExp's ifexp_expr_full_ok is the conditional's: the chain is
 * ok when its operands are, each later operand where the one before
 * evaluates.
 *
 * TOP-LEVEL:
 *   bool_chain_full_ok_def    - the operands' body predicates, in order
 *   bool_chain_expr_full_ok   - the chain's body predicate from its operands'
 *)
Theory bodyFullBoolChain
Ancestors
  bodyFullIfExp exprSimBoolChain bodyFullOfVV bodyFullPreds bodySimFull
  exprSimIfExp exprSimDefs exprLowering

(* Each operand is ok, a later one where the one before evaluates. *)
Definition bool_chain_full_ok_def:
  bool_chain_full_ok cx [] = T /\
  bool_chain_full_ok cx (e::es) =
    (body_expr_full_ok cx e /\
     ((?s tv s'. eval_expr cx e s = (INL tv, s')) ==>
      bool_chain_full_ok cx es))
End

Theorem bool_chain_expr_full_ok:
  !cx ann is_and n e.
    bool_chain_full_ok cx (bool_chain_operands is_and (n - 1) e) ==>
    body_expr_full_ok cx (Builtin ann (BoolChain is_and n) [e])
Proof
  cheat
QED
