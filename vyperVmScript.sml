open HolKernel boolLib bossLib Parse
open listTheory finite_mapTheory
open vyperAstTheory vfmContextTheory

val () = new_theory "vyperVm";

Datatype:
  value
  = VoidV
  | BoolV bool
  | TupleV (value list)
  | ArrayV (value list)
  | IntV int
  | StringV string
  | BytesV (word8 list)
End

Definition evaluate_literal_def:
  evaluate_literal (BoolL b)   = BoolV b ∧
  evaluate_literal (StringL s) = StringV s ∧
  evaluate_literal (BytesL bs) = BytesV bs ∧
  evaluate_literal (IntL i)    = IntV i
End

Datatype:
  expr_result = Err | Vs (value list)
End

Definition evaluate_cmp_def:
  evaluate_cmp Eq    (StringV s1) (StringV s2) = Vs [BoolV (s1 = s2)] ∧
  evaluate_cmp Eq    (IntV i1)    (IntV i2)    = Vs [BoolV (i1 = i2)] ∧
  evaluate_cmp NotEq (StringV s1) (StringV s2) = Vs [BoolV (s1 ≠ s2)] ∧
  evaluate_cmp NotEq (IntV i1)    (IntV i2)    = Vs [BoolV (i1 ≠ i2)] ∧
  evaluate_cmp _ _ _ = Err
End

Definition evaluate_binop_def:
  evaluate_binop Add (IntV i1) (IntV i2) = Vs [IntV (i1 + i2)] ∧
  evaluate_binop Sub (IntV i1) (IntV i2) = Vs [IntV (i1 - i2)] ∧
  evaluate_binop (_: operator) _ _ = Err
End

Definition expr_nodes_def:
  expr_nodes (NamedExpr e1 e2) = 1n + expr_nodes e1 + expr_nodes e2 ∧
  expr_nodes (Name _) = 1 + 1 ∧
  expr_nodes (IfExp e1 e2 e3) = 1 + expr_nodes e1 + expr_nodes e2 + expr_nodes e3 ∧
  expr_nodes (Literal _) = 1 + 1 ∧
  expr_nodes (ArrayLit es) = 1 + LENGTH es + SUM (MAP expr_nodes es) ∧
  expr_nodes (Compare e1 _ e2) = 1 + expr_nodes e1 + 1 + expr_nodes e2 ∧
  expr_nodes (BinOp e1 _ e2) = 1 + expr_nodes e1 + 1 + expr_nodes e2
Termination
  WF_REL_TAC`measure expr_size`
End

Definition evaluate_exps_def:
  evaluate_exps env [Literal l] = Vs [evaluate_literal l] ∧
  evaluate_exps env [ArrayLit es] =
  (case evaluate_exps env es of
        Vs vs => Vs [ArrayV vs]
      | _ => Err) ∧
  evaluate_exps env [Name id] =
  (case FLOOKUP env id of SOME v => Vs [v]
   | _ => Err) ∧
  evaluate_exps env [IfExp e1 e2 e3] =
  (case evaluate_exps env [e1] of Vs [BoolV b] =>
     if b then evaluate_exps env [e2] else evaluate_exps env [e3]
   | _ => Err) ∧
  evaluate_exps env [Compare e1 cmp e2] =
  (case evaluate_exps env [e1; e2] of Vs [v1; v2] =>
     evaluate_cmp cmp v1 v2
   | _ => Err) ∧
  evaluate_exps env [BinOp e1 bop e2] =
  (case evaluate_exps env [e1; e2] of Vs [v1; v2] =>
     evaluate_binop bop v1 v2
   | _ => Err) ∧
  evaluate_exps env [] = Vs [] ∧
  evaluate_exps env [e1] = Err ∧
  evaluate_exps env (e1::es) =
  (case evaluate_exps env [e1] of Vs [v1] =>
    (case evaluate_exps env es of Vs vs => Vs (v1::vs) | x => x)
   | x => x)
Termination
  WF_REL_TAC`measure ((λls. LENGTH ls + SUM (MAP expr_nodes ls)) o SND)`
  \\ rw[expr_nodes_def, ETA_AX]
End

Definition default_value_def:
  default_value (UintT _) = IntV 0 ∧
  default_value (IntT _) = IntV 0 ∧
  default_value (TupleT ts) = TupleV (MAP default_value ts) ∧
  default_value (DynArrayT _ _) = ArrayV [] ∧
  default_value VoidT = VoidV ∧
  default_value BoolT = BoolV F ∧
  default_value StringT = StringV "" ∧
  default_value BytesT = BytesV []
Termination
  WF_REL_TAC ‘measure type_size’
End

Datatype:
  exception
  = BreakException
  | ContinueException
  | ReturnException value
  | RaiseException string
  | AssertException string
  | Error
  | Timeout
End

Datatype:
  function_context = <|
    scopes: (identifier |-> value) list
  ; raised: exception option
  |>
End

Definition initial_function_context_def:
  initial_function_context = <|
    scopes := [FEMPTY]
  ; raised := NONE
  |>
End

Definition raise_def:
  raise err ctx = ctx with raised := SOME err
End

Definition push_scope_def:
  push_scope ctx = ctx with scopes updated_by CONS FEMPTY
End

Definition pop_scope_def:
  pop_scope ctx =
  case ctx.scopes of [] => raise Error ctx
  | (_::rest) => ctx with scopes := rest
End

Definition new_variable_def:
  new_variable id typ ctx =
  case ctx.scopes of [] => raise Error ctx
  | env::rest => if id ∈ FDOM env then raise Error ctx else
    ctx with scopes := (env |+ (id, default_value typ))::rest
End

Definition assign_target_def:
  assign_target id v ctx =
  case ctx.scopes of [] => raise Error ctx
  | env::rest => if id ∉ FDOM env then raise Error ctx else
    (* check that v has same type as current value here ? *)
    ctx with scopes := (env |+ (id, v))::rest
End

(* TODO: use state-exception monad *)
(* TODO: remove clock? it should be bounded... *)

Definition execute_stmts_def:
  execute_stmts n [Pass] ctx = ctx ∧
  execute_stmts n [Continue] ctx = raise ContinueException ctx ∧
  execute_stmts n [Break] ctx = raise BreakException ctx ∧
  execute_stmts n [Raise s] ctx = raise (RaiseException s) ctx ∧
  execute_stmts n [Return NONE] ctx = raise (ReturnException VoidV) ctx ∧
  execute_stmts n [Return (SOME e)] ctx =
  (case ctx.scopes of [] => raise Error ctx | env::_ =>
   (case evaluate_exps env [e] of Vs [v] =>
      raise (ReturnException v) ctx
    | _ => raise Error ctx)) ∧
  execute_stmts n [AnnAssign id typ e] ctx =
  (let ctx = new_variable id typ ctx in
   if IS_SOME ctx.raised then ctx else
   case ctx.scopes of [] => raise Error ctx | env::_ =>
   (case evaluate_exps env [e] of Vs [v] =>
      assign_target id v ctx
    | _ => raise Error ctx)) ∧
  execute_stmts n [Assign id e] ctx =
  (case ctx.scopes of [] => raise Error ctx | env::_ =>
   (case evaluate_exps env [e] of Vs [v] =>
     assign_target id v ctx
    | _ => raise Error ctx)) ∧
  execute_stmts n [If e s1 s2] ctx =
  (case ctx.scopes of [] => raise Error ctx | env::_ =>
   if n = 0 then raise Timeout ctx else
   (case evaluate_exps env [e] of Vs [BoolV b] =>
     execute_stmts (PRE n) (if b then s1 else s2) ctx
    | _ => raise Error ctx)) ∧
  execute_stmts n [For id typ e ss] ctx =
  (case ctx.scopes of [] => raise Error ctx | env::_ =>
   case evaluate_exps env [e] of Vs [ArrayV vs] =>
   let
     ctx = push_scope ctx;
     ctx = new_variable id typ ctx;
   in
     if IS_SOME ctx.raised then ctx else
     if n = 0 then raise Timeout ctx else
       execute_for (PRE n) id typ ss vs ctx
   | _ => raise Error ctx) ∧
  execute_stmts n [_] ctx = raise Error ctx ∧
  execute_stmts n [] ctx = ctx ∧
  execute_stmts n (s1::ss) ctx =
  (if n = 0 then raise Timeout ctx else
    let ctx = execute_stmts (PRE n) [s1] ctx in
      if IS_SOME ctx.raised then ctx else
      execute_stmts (PRE n) ss ctx) ∧
  execute_for n id typ ss [] ctx =
  (let ctx = pop_scope ctx in
    if IS_SOME ctx.raised then ctx else
      pop_scope ctx) ∧
  execute_for n id typ ss (v::vs) ctx =
  (let ctx = assign_target id v ctx in
    if IS_SOME ctx.raised then ctx else
    if n = 0 then raise Timeout ctx else
   let ctx = execute_stmts (PRE n) ss ctx in
    if IS_SOME ctx.raised then ctx else
   execute_for (PRE n) id typ ss vs ctx)
Termination
  WF_REL_TAC`measure (λx. case x of
    (INR (n,_) => n) | (INL (n,_) => n))`
End

Datatype:
  execution_context = <|
    function_contexts: function_context list
  |>
End

val () = export_theory();
