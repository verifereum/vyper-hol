open HolKernel boolLib bossLib Parse
open listTheory finite_mapTheory
open vyperAstTheory vfmContextTheory

val () = new_theory "vyperVm";

Datatype:
  value
  = VoidV
  | BoolV bool
  | TupleV (value list)
  | IntV int
  | StringV string
  | BytesV (word8 list)
End

Datatype:
  function_context = <|
    scopes: identifier |-> value
  |>
End

Datatype:
  execution_context = <|
    function_contexts: function_context list
  |>
End

Definition evaluate_literal_def:
  evaluate_literal (BoolL b)   = BoolV b ∧
  evaluate_literal (StringL s) = StringV s ∧
  evaluate_literal (BytesL bs) = BytesV bs ∧
  evaluate_literal (IntL i)    = IntV i
End

Datatype:
  result = TypeError | Vs (value list)
End

Definition evaluate_cmp_def:
  evaluate_cmp Eq    (StringV s1) (StringV s2) = Vs [BoolV (s1 = s2)] ∧
  evaluate_cmp Eq    (IntV i1)    (IntV i2)    = Vs [BoolV (i1 = i2)] ∧
  evaluate_cmp NotEq (StringV s1) (StringV s2) = Vs [BoolV (s1 ≠ s2)] ∧
  evaluate_cmp NotEq (IntV i1)    (IntV i2)    = Vs [BoolV (i1 ≠ i2)] ∧
  evaluate_cmp _ _ _ = TypeError
End

Definition evaluate_binop_def:
  evaluate_binop Add (IntV i1) (IntV i2) = Vs [IntV (i1 + i2)] ∧
  evaluate_binop Sub (IntV i1) (IntV i2) = Vs [IntV (i1 - i2)] ∧
  evaluate_binop (_: operator) _ _ = TypeError
End

Definition expr_nodes_def:
  expr_nodes (NamedExpr e1 e2) = 1n + expr_nodes e1 + expr_nodes e2 ∧
  expr_nodes (Name _) = 1 + 1 ∧
  expr_nodes (IfExp e1 e2 e3) = 1 + expr_nodes e1 + expr_nodes e2 + expr_nodes e3 ∧
  expr_nodes (Literal _) = 1 + 1 ∧
  expr_nodes (ArrayLit es) = 1 + SUM (MAP expr_nodes es) ∧
  expr_nodes (Compare e1 _ e2) = 1 + expr_nodes e1 + 1 + expr_nodes e2 ∧
  expr_nodes (BinOp e1 _ e2) = 1 + expr_nodes e1 + 1 + expr_nodes e2
Termination
  WF_REL_TAC`measure expr_size`
End

Definition evaluate_exps_def:
  evaluate_exps env [Literal l] = Vs [evaluate_literal l] ∧
  evaluate_exps env [Name id] =
  (case FLOOKUP env id of SOME v => Vs [v]
   | _ => TypeError) ∧
  evaluate_exps env [IfExp e1 e2 e3] =
  (case evaluate_exps env [e1] of Vs [BoolV b] =>
     if b then evaluate_exps env [e2] else evaluate_exps env [e3]
   | _ => TypeError) ∧
  evaluate_exps env [Compare e1 cmp e2] =
  (case evaluate_exps env [e1; e2] of Vs [v1; v2] =>
     evaluate_cmp cmp v1 v2
   | _ => TypeError) ∧
  evaluate_exps env [BinOp e1 bop e2] =
  (case evaluate_exps env [e1; e2] of Vs [v1; v2] =>
     evaluate_binop bop v1 v2
   | _ => TypeError) ∧
  evaluate_exps env [] = Vs [] ∧
  evaluate_exps env [e1] = TypeError ∧
  evaluate_exps env (e1::es) =
  (case evaluate_exps env [e1] of Vs [v1] =>
    (case evaluate_exps env es of Vs vs => Vs (v1::vs) | x => x)
   | x => x)
Termination
  WF_REL_TAC`measure ((λls. LENGTH ls + SUM (MAP expr_nodes ls)) o SND)`
  \\ rw[expr_nodes_def]
End

val () = export_theory();
