open HolKernel boolLib bossLib Parse
open listTheory alistTheory finite_mapTheory
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
  | StructV ((identifier, value) alist)
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
  expr_nodes (GlobalName _) = 1 + 1 ∧
  expr_nodes (IfExp e1 e2 e3) = 1 + expr_nodes e1 + expr_nodes e2 + expr_nodes e3 ∧
  expr_nodes (Literal _) = 1 + 1 ∧
  expr_nodes (ArrayLit es) = 1 + LENGTH es + SUM (MAP expr_nodes es) ∧
  expr_nodes (Compare e1 _ e2) = 1 + expr_nodes e1 + 1 + expr_nodes e2 ∧
  expr_nodes (BinOp e1 _ e2) = 1 + expr_nodes e1 + 1 + expr_nodes e2 ∧
  expr_nodes (Subscript e1 e2) = 1 + 2 + expr_nodes e1 + expr_nodes e2 ∧
  expr_nodes (Attribute e _) = 1 + expr_nodes e + 1
Termination
  WF_REL_TAC`measure expr_size`
End

Type scope = “:identifier |-> value”;

Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME v => SOME v
End

Definition extract_elements_def:
  extract_elements (ArrayV vs) = SOME vs ∧
  extract_elements (TupleV vs) = SOME vs ∧
  extract_elements _ = NONE
End

Definition replace_elements_def:
  replace_elements (ArrayV _) vs = SOME (ArrayV vs) ∧
  replace_elements (TupleV _) vs = SOME (TupleV vs) ∧
  replace_elements _ _ = NONE
End

Definition integer_index_def:
  integer_index vs i =
   if Num i < LENGTH vs then
     SOME $ if 0 ≤ i then Num i else LENGTH vs - Num i
   else NONE
End

Datatype:
  toplevel_value = Value value | HashMap ((value, toplevel_value) alist)
End

Definition evaluate_exps_def:
  evaluate_exps gbs env [Literal l] = Vs [evaluate_literal l] ∧
  evaluate_exps gbs env [ArrayLit es] =
  (case evaluate_exps gbs env es of
        Vs vs => Vs [ArrayV vs]
      | _ => Err) ∧
  evaluate_exps gbs env [Name id] =
  (case lookup_scopes id env of SOME v => Vs [v]
   | _ => Err) ∧
  evaluate_exps gbs env [GlobalName id] =
  (case FLOOKUP gbs id of SOME (Value v) => Vs [v] | _ => Err) ∧
  evaluate_exps gbs env [Subscript e1 e2] =
  (case evaluate_exps gbs env [e1; e2] of Vs [av; IntV i] =>
   (case extract_elements av of SOME vs =>
    (case integer_index vs i of SOME j => Vs [EL j vs]
     | _ => Err) | _ => Err) | _ => Err) ∧
  evaluate_exps gbs env [Attribute e id] =
  (case evaluate_exps gbs env [e] of Vs [StructV kvs] =>
   (case ALOOKUP kvs id of SOME v => Vs [v]
       | _ => Err) | _ => Err) ∧
  evaluate_exps gbs env [IfExp e1 e2 e3] =
  (case evaluate_exps gbs env [e1] of Vs [BoolV b] =>
     if b then evaluate_exps gbs env [e2] else evaluate_exps gbs env [e3]
   | _ => Err) ∧
  evaluate_exps gbs env [Compare e1 cmp e2] =
  (case evaluate_exps gbs env [e1; e2] of Vs [v1; v2] =>
     evaluate_cmp cmp v1 v2
   | _ => Err) ∧
  evaluate_exps gbs env [BinOp e1 bop e2] =
  (case evaluate_exps gbs env [e1; e2] of Vs [v1; v2] =>
     evaluate_binop bop v1 v2
   | _ => Err) ∧
  evaluate_exps gbs env [] = Vs [] ∧
  evaluate_exps gbs env [e1] = Err ∧
  evaluate_exps gbs env (e1::es) =
  (case evaluate_exps gbs env [e1] of Vs [v1] =>
    (case evaluate_exps gbs env es of Vs vs => Vs (v1::vs) | x => x)
   | x => x)
Termination
  WF_REL_TAC`measure ((λls. LENGTH ls + SUM (MAP expr_nodes ls)) o SND o SND)`
  \\ rw[expr_nodes_def, ETA_AX]
End

Definition default_value_def:
  default_value (BaseT (UintT _)) = IntV 0 ∧
  default_value (BaseT (IntT _)) = IntV 0 ∧
  default_value (TupleT ts) = TupleV (MAP default_value ts) ∧
  default_value (DynArrayT _ _) = ArrayV [] ∧
  default_value VoidT = VoidV ∧
  default_value (BaseT BoolT) = BoolV F ∧
  default_value (BaseT StringT) = StringV "" ∧
  default_value (BaseT BytesT) = BytesV []
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
    scopes: scope list
  ; globals: identifier |-> toplevel_value
  ; raised: exception option
  |>
End

Definition initial_function_context_def:
  initial_function_context = <|
    scopes := [FEMPTY]
  ; globals := FEMPTY
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

Type containing_scope = “: scope list # scope # scope list”;

Definition find_containing_scope_def:
  find_containing_scope id [] = NONE : containing_scope option ∧
  find_containing_scope id (env::rest) =
  if id ∈ FDOM env then SOME ([], env, rest)
  else OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
End

Datatype:
  location
  = ScopedVar containing_scope identifier
  | Global identifier
End

Datatype:
  subscript
  = IntSubscript int
  | StrSubscript string
  | AttrSubscript identifier
End

Datatype:
  assignment_value
  = BaseTargetV location (subscript list)
  | TupleTargetV (assignment_value list)
End

Definition add_subscript_def:
  add_subscript (l: location, ls) (i: subscript) = (l, i::ls)
End

Definition evaluate_base_target_def:
  evaluate_base_target gbs env (NameTarget id) =
    OPTION_MAP (λcs. (ScopedVar cs id,[])) (find_containing_scope id env) ∧
  evaluate_base_target gbs env (GlobalNameTarget id) = SOME $ (Global id, []) ∧
  evaluate_base_target gbs env (SubscriptTarget t e) =
  (case evaluate_base_target gbs env t of NONE => NONE | SOME v =>
   (case evaluate_exps gbs env [e] of Vs [IntV i] =>
      SOME $ add_subscript v (IntSubscript i)
    | _ => NONE)) ∧
  evaluate_base_target gbs env (AttributeTarget t id) =
  (case evaluate_base_target gbs env t of NONE => NONE | SOME v =>
   SOME $ add_subscript v (AttrSubscript id))
End

Definition evaluate_target_def:
  evaluate_target gbs env (BaseTarget b) =
  OPTION_MAP (UNCURRY BaseTargetV) (evaluate_base_target gbs env b) ∧
  evaluate_target gbs env (TupleTarget []) = SOME $ TupleTargetV [] ∧
  evaluate_target gbs env (TupleTarget (t::ts)) =
  (case evaluate_target gbs env t of NONE => NONE | SOME v =>
   case evaluate_target gbs env (TupleTarget ts) of SOME (TupleTargetV vs) =>
     SOME (TupleTargetV (v::vs)) | _ => NONE)
End

Definition set_variable_def:
  set_variable id v ctx =
  case find_containing_scope id ctx.scopes of
    NONE => raise Error ctx
  | SOME (pre, env, rest) =>
    (* check that v has same type as current value here ? *)
    ctx with scopes := pre ++ (env |+ (id, v))::rest
End

Definition assign_subscripts_def:
  assign_subscripts a [] v = SOME v ∧
  assign_subscripts a ((IntSubscript i)::is) v =
  (case extract_elements a of SOME vs =>
   (case integer_index vs i of SOME j =>
    (case assign_subscripts (EL j vs) is v of SOME vj =>
       replace_elements a (TAKE j vs ++ [vj] ++ DROP (SUC j) vs)
     | _ => NONE)
    | _ => NONE)
   | _ => NONE) ∧
  assign_subscripts a _ v = NONE (* TODO: handle AttrSubscript *)
End

Definition assign_target_def:
  assign_target (BaseTargetV (ScopedVar (pre,env,rest) id) is) v ctx =
  (case FLOOKUP env id of SOME a =>
   (case assign_subscripts a is v of SOME a' =>
      ctx with scopes := pre ++ (env |+ (id, a'))::rest
    | _ => raise Error ctx)
   | _ => raise Error ctx) ∧
  assign_target (BaseTargetV (Global id) is) v ctx =
  (* TODO: add assignment to hashmaps *)
  (case FLOOKUP ctx.globals id of SOME (Value a) =>
   (case assign_subscripts a is v of SOME a' =>
     ctx with globals := ctx.globals |+ (id, Value a')
    | _ => raise Error ctx)
   | _ => raise Error ctx) ∧
  assign_target _ _ ctx = raise Error ctx (* TODO: handle TupleTargetV *)
End

(* TODO: remove clock:
* - ensure For statement bound (DynArray max size, or range max) is present on syntax
* - define bound on execution steps for statements syntactically
* - use that to craft the termination measure *)

(* TODO: use state-exception monad *)

Definition execute_stmts_def:
  execute_stmts n [Pass] ctx = ctx ∧
  execute_stmts n [Continue] ctx = raise ContinueException ctx ∧
  execute_stmts n [Break] ctx = raise BreakException ctx ∧
  execute_stmts n [Raise s] ctx = raise (RaiseException s) ctx ∧
  execute_stmts n [Return NONE] ctx = raise (ReturnException VoidV) ctx ∧
  execute_stmts n [Return (SOME e)] ctx =
  (case evaluate_exps ctx.globals ctx.scopes [e] of Vs [v] =>
     raise (ReturnException v) ctx
   | _ => raise Error ctx) ∧
  execute_stmts n [AnnAssign id typ e] ctx =
  (let ctx = new_variable id typ ctx in
   if IS_SOME ctx.raised then ctx else
   (case evaluate_exps ctx.globals ctx.scopes [e] of Vs [v] =>
      set_variable id v ctx
    | _ => raise Error ctx)) ∧
  execute_stmts n [AugAssign id bop e2] ctx =
  (case lookup_scopes id ctx.scopes of NONE => raise Error ctx | SOME v1 =>
   case evaluate_exps ctx.globals ctx.scopes [e2] of Vs [v2] =>
   (case evaluate_binop bop v1 v2 of Vs [v] =>
      set_variable id v ctx
    | _ => raise Error ctx)
   | _ => raise Error ctx) ∧
  execute_stmts n [Assign tgt e] ctx =
   (case evaluate_exps ctx.globals ctx.scopes [e] of Vs [v] =>
    (case evaluate_target ctx.globals ctx.scopes tgt of SOME tv =>
      assign_target tv v ctx
     | _ => raise Error ctx)
    | _ => raise Error ctx) ∧
  execute_stmts n [If e s1 s2] ctx =
  (if n = 0 then raise Timeout ctx else
   (case evaluate_exps ctx.globals ctx.scopes [e] of Vs [BoolV b] =>
     execute_stmts (PRE n) (if b then s1 else s2) ctx
    | _ => raise Error ctx)) ∧
  execute_stmts n [For id typ e ss] ctx =
  (case evaluate_exps ctx.globals ctx.scopes [e] of Vs [ArrayV vs] =>
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
  execute_for n id typ ss [] ctx = pop_scope ctx ∧
  execute_for n id typ ss (v::vs) ctx =
  (let ctx = push_scope ctx in
   let ctx = set_variable id v ctx in
    if IS_SOME ctx.raised then ctx else
    if n = 0 then raise Timeout ctx else
   let ctx = execute_stmts (PRE n) ss ctx in
    if IS_SOME ctx.raised then ctx else
   let ctx = pop_scope ctx in
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
