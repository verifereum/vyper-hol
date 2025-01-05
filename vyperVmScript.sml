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

Datatype:
  toplevel_value = Value value | HashMap ((value, toplevel_value) alist)
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

Type scope = “:identifier |-> value”;

Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME v => SOME v
End

Datatype:
  expr_continuation
  = StartExpr expr
  (*
  | NamedExprK1 expr_continuation expr
  | NamedExprK2 value expr_continuation
  *)
  | IfExpK expr_continuation expr expr
  | ArrayLitK (value list) expr_continuation (expr list)
  | SubscriptK1 expr_continuation expr
  | SubscriptK2 value expr_continuation
  | AttributeK expr_continuation identifier
  | CompareK1 expr_continuation cmpop expr
  | CompareK2 value cmpop expr_continuation
  | BinOpK1 expr_continuation operator expr
  | BinOpK2 value operator expr_continuation
  | CallK identifier (value list) expr_continuation (expr list)
  | LiftCall identifier (value list) expr_continuation
  | DoneExpr value
  | ReturnExpr
  | ErrorExpr
End

Type containing_scope = “: scope list # scope # scope list”;

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

Datatype:
  base_tgt_continuation
  = StartBaseTgt base_assignment_target
  | SubscriptTargetK1 base_tgt_continuation expr
  | SubscriptTargetK2 location (subscript list) expr_continuation
  | AttributeTargetK base_tgt_continuation identifier
  | LiftCallBaseTgt identifier (value list) base_tgt_continuation
  | DoneBaseTgt location (subscript list)
End

Datatype:
  tgt_continuation
  = StartTgt assignment_target
  | TupleTargetK (assignment_value list) tgt_continuation (assignment_target list)
  | BaseTargetK base_tgt_continuation
  | LiftCallTgt identifier (value list) tgt_continuation
  | DoneTgt assignment_value
  | ErrorTgt
End

Datatype:
  exception
  = RaiseException string
  | AssertException string
  | Error
  | ExternalReturn value
End

Datatype:
  stmt_continuation
  = StartK stmt
  | IfK expr_continuation (stmt list) (stmt list)
  | AssertK expr_continuation string
  | ReturnSomeK expr_continuation
  | AssignK1 tgt_continuation expr
  | AssignK2 assignment_value expr_continuation
  | AugAssignK identifier operator expr_continuation
  | AnnAssignK identifier type expr_continuation
  | ForK identifier type expr_continuation (stmt list)
  | DoneK
  | ExceptionK exception
End

Definition evaluate_literal_def:
  evaluate_literal (BoolL b)   = BoolV b ∧
  evaluate_literal (StringL s) = StringV s ∧
  evaluate_literal (BytesL bs) = BytesV bs ∧
  evaluate_literal (IntL i)    = IntV i
End

Definition evaluate_cmp_def:
  evaluate_cmp Eq    (StringV s1) (StringV s2) = DoneExpr (BoolV (s1 = s2)) ∧
  evaluate_cmp Eq    (IntV i1)    (IntV i2)    = DoneExpr (BoolV (i1 = i2)) ∧
  evaluate_cmp NotEq (StringV s1) (StringV s2) = DoneExpr (BoolV (s1 ≠ s2)) ∧
  evaluate_cmp NotEq (IntV i1)    (IntV i2)    = DoneExpr (BoolV (i1 ≠ i2)) ∧
  evaluate_cmp _ _ _ = ErrorExpr
End

Definition evaluate_binop_def:
  evaluate_binop Add (IntV i1) (IntV i2) = DoneExpr (IntV (i1 + i2)) ∧
  evaluate_binop Sub (IntV i1) (IntV i2) = DoneExpr (IntV (i1 - i2)) ∧
  evaluate_binop (_: operator) _ _ = ErrorExpr
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

Definition evaluate_subscript_def:
  evaluate_subscript av (IntV i) =
  (case extract_elements av of SOME vs =>
    (case integer_index vs i of SOME j => DoneExpr (EL j vs)
     | _ => ErrorExpr)
   | _ => ErrorExpr) ∧
  evaluate_subscript _ _ = ErrorExpr
End

Definition evaluate_attribute_def:
  evaluate_attribute (StructV kvs) id =
  (case ALOOKUP kvs id of SOME v => DoneExpr v
   | _ => ErrorExpr) ∧
  evaluate_attribute _ _ = ErrorExpr
End

Definition step_expr_def:
  step_expr gbs env (StartExpr (Literal l)) =
    DoneExpr (evaluate_literal l) ∧
  step_expr gbs env (StartExpr (ArrayLit [])) =
    DoneExpr (ArrayV []) ∧
  step_expr gbs env (StartExpr (ArrayLit (e::es))) =
    ArrayLitK [] (StartExpr e) es ∧
  step_expr gbs env (StartExpr (Name id)) =
    (case lookup_scopes id env
     of SOME v => DoneExpr v
      | _ => ErrorExpr) ∧
  step_expr gbs env (StartExpr (GlobalName id)) =
    (case FLOOKUP gbs id
     of SOME (Value v) => DoneExpr v
      | _ => ErrorExpr) ∧
  step_expr gbs env (StartExpr (Subscript e1 e2)) =
    SubscriptK1 (StartExpr e1) e2 ∧
  step_expr gbs env (StartExpr (Attribute e id)) =
    AttributeK (StartExpr e) id ∧
  step_expr gbs env (StartExpr (IfExp e1 e2 e3)) =
    IfExpK (StartExpr e1) e2 e3 ∧
  step_expr gbs env (StartExpr (Compare e1 cmp e2)) =
    CompareK1 (StartExpr e1) cmp e2 ∧
  step_expr gbs env (StartExpr (BinOp e1 bop e2)) =
    BinOpK1 (StartExpr e1) bop e2 ∧
  step_expr gbs env (StartExpr (Call id [])) =
    LiftCall id [] ReturnExpr ∧
  step_expr gbs env (StartExpr (Call id (e::es))) =
    CallK id [] (StartExpr e) es ∧
  (*
  step_expr gbs env (NamedExprK1 k e) =
    (case step_expr gbs env k
     of ErrorExpr => ErrorExpr
      | DoneExpr v => NamedExprK2 v (StartExpr e)
      | LiftCall id vs k => LiftCall id vs (NamedExprK1 k e)
      | k => NamedExprK1 k e) ∧
  step_expr gbs env (NamedExprK2 v1 k) =
    (case step_expr gbs env k
     of ErrorExpr => ErrorExpr
      | DoneExpr v2 =>
  *)
  step_expr gbs env (IfExpK k e2 e3) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v1 => (case v1 of BoolV b => StartExpr (if b then e2 else e3)
                               | _ => ErrorExpr)
    | LiftCall id vs k => LiftCall id vs (IfExpK k e2 e3)
    | k => IfExpK k e2 e3) ∧
  step_expr gbs env (ArrayLitK vs k es) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v =>
        (case es of (e::es) => ArrayLitK (SNOC v vs) (StartExpr e) es
                  | [] => DoneExpr (ArrayV (SNOC v vs)))
    | LiftCall id as k => LiftCall id as (ArrayLitK vs k es)
    | k => ArrayLitK vs k es) ∧
  step_expr gbs env (SubscriptK1 k e) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v => SubscriptK2 v (StartExpr e)
    | LiftCall id vs k => LiftCall id vs (SubscriptK1 k e)
    | k => SubscriptK1 k e) ∧
  step_expr gbs env (SubscriptK2 v1 k) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v2 => evaluate_subscript v1 v2
    | LiftCall id vs k => LiftCall id vs (SubscriptK2 v1 k)
    | k => SubscriptK2 v1 k) ∧
  step_expr gbs env (AttributeK k id) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v => evaluate_attribute v id
    | LiftCall id vs k => LiftCall id vs (AttributeK k id)
    | k => AttributeK k id) ∧
  step_expr gbs env (CompareK1 k cmp e2) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v1 => CompareK2 v1 cmp (StartExpr e2)
    | LiftCall id vs k => LiftCall id vs (CompareK1 k cmp e2)
    | k => CompareK1 k cmp e2) ∧
  step_expr gbs env (CompareK2 v1 cmp k) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v2 => evaluate_cmp cmp v1 v2
    | LiftCall id vs k => LiftCall id vs (CompareK2 v1 cmp k)
    | k => CompareK2 v1 cmp k) ∧
  step_expr gbs env (BinOpK1 k bop e2) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v1 => BinOpK2 v1 bop (StartExpr e2)
    | LiftCall id vs k => LiftCall id vs (BinOpK1 k bop e2)
    | k => BinOpK1 k bop e2) ∧
  step_expr gbs env (BinOpK2 v1 bop k) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v2 => evaluate_binop bop v1 v2
    | LiftCall id vs k => LiftCall id vs (BinOpK2 v1 bop k)
    | k => BinOpK2 v1 bop k) ∧
  step_expr gbs env (CallK id vs k es) =
  (case step_expr gbs env k
   of ErrorExpr => ErrorExpr
    | DoneExpr v =>
        (case es of (e::es) => CallK id (SNOC v vs) (StartExpr e) es
                  | [] => LiftCall id (SNOC v vs) ReturnExpr)
    | LiftCall id vs k => LiftCall id vs (CallK id vs k es)
    | k => CallK id vs k es) ∧
  step_expr gbs env (LiftCall id vs k) = LiftCall id vs k ∧
  step_expr gbs env (DoneExpr v) = DoneExpr v ∧
  step_expr gbs env ReturnExpr = ReturnExpr ∧
  step_expr gbs env ErrorExpr = ErrorExpr
End

Datatype:
  loop_info = <|
    loop_var: identifier
  ; loop_first_stmt: stmt
  ; loop_rest_stmts: stmt list
  ; remaining_values: value list
  |>
End

Datatype:
  function_context =
  <| scopes: scope list
   ; current_stmt: stmt_continuation
   ; remaining_stmts: stmt list
   ; loop: loop_info option
   |>
End

Datatype:
  execution_context = <|
    current_fc : function_context
  ; call_stack : function_context list
  ; globals: identifier |-> toplevel_value
  ; contract: toplevel list
  |>
End

Definition initial_function_context_def:
  initial_function_context args ss = <|
    scopes := [args]
  ; current_stmt := (case ss of s::_ => StartK s | _ => ExceptionK Error)
  ; remaining_stmts := TL ss
  ; loop := NONE
  |>
End

(* TODO: assumes unique identifiers, but should check? *)
Definition initial_globals_def:
  initial_globals [] = FEMPTY ∧
  initial_globals (VariableDecl id typ _ Storage :: ts) =
  initial_globals ts |+ (id, Value $ default_value typ) ∧
  initial_globals (VariableDecl id typ _ Transient :: ts) =
  initial_globals ts |+ (id, Value $ default_value typ) ∧
  (* TODO: handle Constants and  Immutables *)
  initial_globals (t :: ts) = initial_globals ts
  (* TODO: hashmap toplevels *)
End

Definition initial_execution_context_def:
  initial_execution_context ts fc = <|
    current_fc := fc
  ; call_stack := []
  ; globals := initial_globals ts
  ; contract := ts
  |>
End

Definition raise_def:
  raise err ctx = ctx with current_fc updated_by
    (λfc. fc with current_stmt := ExceptionK err)
End

Definition push_scope_def:
  push_scope ctx =
    ctx with current_fc updated_by (λfc. fc with scopes updated_by CONS FEMPTY)
End

Definition pop_scope_def:
  pop_scope ctx =
  case ctx.current_fc.scopes
    of [] => raise Error ctx
     | (_::rest) => ctx with current_fc updated_by (λfc. fc with scopes := rest)
End

Definition new_variable_def:
  new_variable id typ ctx =
  case ctx.current_fc.scopes
    of [] => raise Error ctx
     | env::rest =>
         if id ∈ FDOM env then raise Error ctx
         else ctx with current_fc updated_by
           (λfc. fc with scopes := (env |+ (id, default_value typ))::rest)
End

Definition find_containing_scope_def:
  find_containing_scope id [] = NONE : containing_scope option ∧
  find_containing_scope id (env::rest) =
  if id ∈ FDOM env then SOME ([], env, rest)
  else OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
End

Definition step_base_target_def:
  step_base_target gbs env (StartBaseTgt (NameTarget id)) =
    (case find_containing_scope id env
     of SOME cs => SOME $ DoneBaseTgt (ScopedVar cs id) []
      | _ => NONE) ∧
  step_base_target gbs env (StartBaseTgt (GlobalNameTarget id)) =
    SOME $ DoneBaseTgt (Global id) [] ∧
  step_base_target gbs env (StartBaseTgt (SubscriptTarget t e)) =
  SOME $ SubscriptTargetK1 (StartBaseTgt t) e ∧
  step_base_target gbs env (StartBaseTgt (AttributeTarget t id)) =
  SOME $ AttributeTargetK (StartBaseTgt t) id ∧
  step_base_target gbs env (SubscriptTargetK1 k e) =
    (case step_base_target gbs env k of
     | SOME (DoneBaseTgt l s) =>
         SOME $ SubscriptTargetK2 l s (StartExpr e)
     | SOME (LiftCallBaseTgt fn vs k) =>
         SOME $ LiftCallBaseTgt fn vs (SubscriptTargetK1 k e)
     | SOME k => SOME $ SubscriptTargetK1 k e
     | _ => NONE) ∧
  step_base_target gbs env (SubscriptTargetK2 l s k) =
   (case step_expr gbs env k
    of DoneExpr (IntV i) => SOME $ DoneBaseTgt l ((IntSubscript i)::s)
     | DoneExpr _ => NONE
     | ErrorExpr => NONE
     | LiftCall fn vs k => SOME $ LiftCallBaseTgt fn vs (SubscriptTargetK2 l s k)
     | k => SOME $ SubscriptTargetK2 l s k) ∧
  step_base_target gbs env (AttributeTargetK k id) =
  (case step_base_target gbs env k
   of NONE => NONE
    | SOME (DoneBaseTgt l s) =>
        SOME $ DoneBaseTgt l ((AttrSubscript id)::s)
    | SOME (LiftCallBaseTgt fn vs k) =>
        SOME $ LiftCallBaseTgt fn vs (AttributeTargetK k id)
    | SOME k => SOME $ AttributeTargetK k id
    | _ => NONE)
End

Definition step_target_def:
  step_target gbs env (StartTgt (BaseTarget b)) =
    BaseTargetK (StartBaseTgt b) ∧
  step_target gbs env (StartTgt (TupleTarget [])) =
    DoneTgt (TupleTargetV []) ∧
  step_target gbs env (StartTgt (TupleTarget (t::ts))) =
    TupleTargetK [] (StartTgt t) ts ∧
  step_target gbs env (TupleTargetK vs k ts) =
  (case step_target gbs env k
   of DoneTgt v =>
     (case ts of [] => DoneTgt (TupleTargetV (SNOC v vs))
               | (t::ts) => TupleTargetK (SNOC v vs) (StartTgt t) ts)
    | LiftCallTgt fn as k =>
        LiftCallTgt fn as (TupleTargetK vs k ts)
    | ErrorTgt => ErrorTgt
    | k => TupleTargetK vs k ts) ∧
  step_target gbs env (BaseTargetK k) =
  (case step_base_target gbs env k
   of SOME (DoneBaseTgt l s) => DoneTgt $ BaseTargetV l s
    | SOME (LiftCallBaseTgt fn vs k) => LiftCallTgt fn vs (BaseTargetK k)
    | SOME k => BaseTargetK k
    | _ => ErrorTgt) ∧
  step_target gbs env (LiftCallTgt fn vs k) = LiftCallTgt fn vs k ∧
  step_target gbs env (DoneTgt v) = DoneTgt v ∧
  step_target gbs env _ = ErrorTgt
End

Definition set_variable_def:
  set_variable id v ctx =
  case find_containing_scope id ctx.current_fc.scopes
    of NONE => raise Error ctx
     | SOME (pre, env, rest) =>
         (* check that v has same type as current value here ? *)
         ctx with current_fc updated_by
           (λfc. fc with scopes := pre ++ (env |+ (id, v))::rest)
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
        ctx with current_fc updated_by
          (λfc. fc with scopes := pre ++ (env |+ (id, a'))::rest)
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

(* TODO: check types? *)
Definition bind_arguments_def:
  bind_arguments ([]: argument list) [] = SOME (FEMPTY: scope) ∧
  bind_arguments ((id, typ)::params) (v::vs) =
    OPTION_MAP (λm. m |+ (id, v)) (bind_arguments params vs) ∧
  bind_arguments _ _ = NONE
End

Definition lookup_external_function_def:
  lookup_external_function name [] = NONE ∧
  lookup_external_function name (FunctionDef id External args ret body :: ts) =
  (if id = name then SOME (args, ret, body)
   else lookup_external_function name ts) ∧
  lookup_external_function name (_ :: ts) =
    lookup_external_function name ts
End

Definition push_call_def:
  push_call fn args ctx =
  case lookup_external_function fn ctx.contract of
  | SOME (params, ret, body) =>
    (case bind_arguments params args of
     | SOME env =>
         let fc = initial_function_context env body in
         ctx with <|
           call_stack updated_by CONS ctx.current_fc
         ; current_fc := fc |>
     | _ => raise Error ctx)
  | _ => raise Error ctx
End

Definition update_current_stmt_def:
  update_current_statement st ctx =
  ctx with current_fc updated_by
    (λfc. fc with current_stmt := st)
End

Definition return_expr_def:
  return_expr v (StartExpr _) = ErrorExpr ∧
  return_expr v (IfExpK k e1 e2) = IfExpK (return_expr v k) e1 e2  ∧
  return_expr v (ArrayLitK vs k es) = ArrayLitK vs (return_expr v k) es ∧
  return_expr v (SubscriptK1 k e) = SubscriptK1 (return_expr v k) e ∧
  return_expr v (SubscriptK2 v k) = SubscriptK2 v (return_expr v k) ∧
  return_expr v (AttributeK k id) = AttributeK (return_expr v k) id ∧
  return_expr v (CompareK1 k cmp e) = CompareK1 (return_expr v k) cmp e ∧
  return_expr v (CompareK2 v cmp k) = CompareK2 v cmp (return_expr v k) ∧
  return_expr v (BinOpK1 k bop e) = BinOpK1 (return_expr v k) bop e ∧
  return_expr v (BinOpK2 v bop k) = BinOpK2 v bop (return_expr v k) ∧
  return_expr v (CallK id vs k es) = CallK id vs (return_expr v k) es ∧
  return_expr v (LiftCall fn vs k) = LiftCall fn vs (return_expr v k) ∧
  return_expr v (DoneExpr _) = ErrorExpr ∧
  return_expr v ReturnExpr = DoneExpr v ∧
  return_expr v ErrorExpr = ErrorExpr
End

Definition return_base_tgt_def:
  return_base_tgt v (StartBaseTgt _) = NONE ∧
  return_base_tgt v (SubscriptTargetK1 k e) =
    OPTION_MAP (λk. SubscriptTargetK1 k e) (return_base_tgt v k) ∧
  return_base_tgt v (SubscriptTargetK2 l s k) =
    SOME (SubscriptTargetK2 l s (return_expr v k)) ∧
  return_base_tgt v (AttributeTargetK k id) =
    OPTION_MAP (λk. AttributeTargetK k id) (return_base_tgt v k) ∧
  return_base_tgt v (LiftCallBaseTgt fn vs k) =
    OPTION_MAP (λk. LiftCallBaseTgt fn vs k) (return_base_tgt v k) ∧
  return_base_tgt _ _ = NONE
End

Definition return_tgt_def:
  return_tgt v (StartTgt _) = ErrorTgt ∧
  return_tgt v (TupleTargetK vs k as) =
    TupleTargetK vs (return_tgt v k) as ∧
  return_tgt v (BaseTargetK t) =
    (case return_base_tgt v t of NONE => ErrorTgt
        | SOME t => BaseTargetK t) ∧
  return_tgt v (LiftCallTgt fn vs k) =
    LiftCallTgt fn vs (return_tgt v k) ∧
  return_tgt v (DoneTgt _) = ErrorTgt ∧
  return_tgt v ErrorTgt = ErrorTgt
End

Definition return_def:
  return v (ForK id typ k ss) = ForK id typ (return_expr v k) ss ∧
  return v (IfK k s1 s2) = IfK (return_expr v k) s1 s2 ∧
  return v (AssertK k s) = AssertK (return_expr v k) s ∧
  return v (ReturnSomeK k) = ReturnSomeK (return_expr v k) ∧
  return v (AssignK1 t e) = AssignK1 (return_tgt v t) e ∧
  return v (AssignK2 a k) = AssignK2 a (return_expr v k) ∧
  return v (AugAssignK id op k) = AugAssignK id op (return_expr v k) ∧
  return v (AnnAssignK id typ k) = AnnAssignK id typ (return_expr v k) ∧
  return v _ = ExceptionK Error
End

Definition pop_call_def:
  pop_call v ctx =
  case ctx.call_stack of fc::fcs =>
    if IS_SOME fc.loop then
      pop_call v (ctx with call_stack := fcs)
    else
      ctx with <|
          current_fc := fc with current_stmt updated_by return v
        ; call_stack := fcs
        |>
  | _ => raise (ExternalReturn v) ctx
Termination
  WF_REL_TAC`measure (λx. LENGTH (SND x).call_stack)` \\ rw[]
End

Definition set_stmt_def:
  set_stmt k ctx =
    ctx with current_fc updated_by (λfc. fc with current_stmt := k)
End

Definition exception_raised_def:
  exception_raised ctx <=>
  case ctx.current_fc.current_stmt of ExceptionK _ => T | _ => F
End

Definition push_loop_def:
  push_loop id typ (v::vs) (s::ss) ctx =
    ctx with <|
      call_stack updated_by CONS ctx.current_fc
    ; current_fc := <|
        scopes := (FEMPTY |+ (id,v))::ctx.current_fc.scopes
      ; current_stmt := (StartK s)
      ; remaining_stmts := ss
      ; loop := SOME <|
          loop_var := id
        ; remaining_values := vs
        ; loop_first_stmt := s
        ; loop_rest_stmts := ss
        |>
      |>
    |> ∧
  push_loop _ _ [] (_::_) ctx = set_stmt DoneK ctx ∧
  push_loop _ _ _ _ ctx = raise Error ctx
End

Definition pop_loop_def:
  pop_loop ctx =
  case ctx.call_stack of
     | [] => raise Error ctx
     | fc::fcs => ctx with <| current_fc := fc; call_stack := fcs |>
End

Definition next_iteration_def:
  next_iteration li ctx =
  case li.remaining_values of [] => pop_loop ctx
     | v::vs => ctx with current_fc updated_by (λfc.
        fc with <| scopes updated_by CONS (FEMPTY |+ (li.loop_var, v))
                 ; current_stmt := StartK li.loop_first_stmt
                 ; remaining_stmts := li.loop_rest_stmts
                 ; loop := SOME (li with remaining_values := vs) |>)
End

Definition continue_loop_def:
  continue_loop ctx =
  case ctx.current_fc.loop of SOME li => (
    let ctx = pop_scope ctx in
      if exception_raised ctx then ctx else
        next_iteration li ctx
  ) | _ => raise Error ctx
End

Definition break_loop_def:
  break_loop ctx =
  case ctx.current_fc.loop of SOME li => (
    let ctx = pop_scope ctx in
      if exception_raised ctx then ctx else
        pop_loop ctx
  ) | _ => raise Error ctx
End

Definition next_stmt_def:
  next_stmt ctx =
  case ctx.current_fc.remaining_stmts of s::ss =>
    ctx with current_fc updated_by (λfc.
      fc with <| current_stmt := StartK s
               ; remaining_stmts := ss |>)
  | _ => (case ctx.current_fc.loop
            of NONE => pop_call VoidV ctx
             | SOME li => next_iteration li ctx)
End

Definition step_stmt_def:
  step_stmt ctx =
  let fc = ctx.current_fc in
  (case fc.current_stmt of
      | StartK Pass => set_stmt DoneK ctx
      | StartK Continue => continue_loop ctx
      | StartK Break => break_loop ctx
      | StartK (Raise s) => raise (RaiseException s) ctx
      | StartK (Assert e s) => set_stmt (AssertK (StartExpr e) s) ctx
      | StartK (Return NONE) => pop_call VoidV ctx
      | StartK (Return (SOME e)) =>
          set_stmt (ReturnSomeK (StartExpr e)) ctx
      | StartK (AnnAssign id typ e) =>
          set_stmt (AnnAssignK id typ (StartExpr e)) ctx
      | StartK (AugAssign id bop e) =>
          set_stmt (AugAssignK id bop (StartExpr e)) ctx
      | StartK (Assign tgt e) =>
          set_stmt (AssignK1 (StartTgt tgt) e) ctx
      | StartK (If e s1 s2) =>
          set_stmt (IfK (StartExpr e) s1 s2) ctx
      | StartK (For id typ e s) =>
          set_stmt (ForK id typ (StartExpr e) s) ctx
      | IfK (DoneExpr (BoolV b)) s1 s2 => (
          case (if b then s1 else s2) of s::ss =>
            ctx with current_fc := fc with
              <| current_stmt := StartK s
               ; remaining_stmts updated_by (λx. ss ++ x) |>
          | _ => raise Error ctx)
      | IfK (DoneExpr _) _ _ => raise Error ctx
      | IfK ErrorExpr _ _ => raise Error ctx
      | IfK ReturnExpr _ _ => raise Error ctx
      | IfK (LiftCall fn vs k) s1 s2 =>
          push_call fn vs
            (set_stmt (IfK k s1 s2) ctx)
      | IfK k s1 s2 =>
          set_stmt
            (IfK (step_expr ctx.globals fc.scopes k) s1 s2) ctx
      | AssertK (DoneExpr (BoolV b)) s => (
          if b then set_stmt DoneK ctx
          else raise (AssertException s) ctx)
      | AssertK (DoneExpr _) _ => raise Error ctx
      | AssertK ErrorExpr _ => raise Error ctx
      | AssertK ReturnExpr _ => raise Error ctx
      | AssertK (LiftCall fn vs k) s =>
          push_call fn vs
            (set_stmt (AssertK k s) ctx)
      | AssertK k s =>
          set_stmt (AssertK (step_expr ctx.globals fc.scopes k) s) ctx
      | ReturnSomeK (DoneExpr v) => pop_call v ctx
      | ReturnSomeK ErrorExpr => raise Error ctx
      | ReturnSomeK ReturnExpr => raise Error ctx
      | ReturnSomeK (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (ReturnSomeK k) ctx)
      | ReturnSomeK k =>
          set_stmt
            (ReturnSomeK (step_expr ctx.globals fc.scopes k)) ctx
      | AssignK1 (DoneTgt av) e =>
          set_stmt (AssignK2 av (StartExpr e)) ctx
      | AssignK1 ErrorTgt e => raise Error ctx
      | AssignK1 (LiftCallTgt fn vs tk) e =>
          push_call fn vs
            (set_stmt (AssignK1 tk e) ctx)
      | AssignK1 tk e =>
          set_stmt
            (AssignK1 (step_target ctx.globals fc.scopes tk) e) ctx
      | AssignK2 tv (DoneExpr v) =>
          set_stmt DoneK (assign_target tv v ctx)
      | AssignK2 tv ErrorExpr => raise Error ctx
      | AssignK2 tv ReturnExpr => raise Error ctx
      | AssignK2 tv (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AssignK2 tv k) ctx)
      | AssignK2 tv k =>
          set_stmt
            (AssignK2 tv (step_expr ctx.globals fc.scopes k)) ctx
      | AugAssignK id bop (DoneExpr v2) =>
        (case lookup_scopes id fc.scopes
           of NONE => raise Error ctx
            | SOME v1 =>
              (case evaluate_binop bop v1 v2
                 of DoneExpr v => set_stmt DoneK (set_variable id v ctx)
                  | _ => raise Error ctx))
      | AugAssignK id bop ErrorExpr => raise Error ctx
      | AugAssignK id bop ReturnExpr => raise Error ctx
      | AugAssignK id bop (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AugAssignK id bop k) ctx)
      | AugAssignK id bop k =>
          set_stmt
            (AugAssignK id bop (step_expr ctx.globals fc.scopes k)) ctx
      | AnnAssignK id typ (DoneExpr v) => (
          let ctx = new_variable id typ ctx in
            if exception_raised ctx then ctx else
              set_stmt DoneK (set_variable id v ctx))
      | AnnAssignK id typ ErrorExpr => raise Error ctx
      | AnnAssignK id typ ReturnExpr => raise Error ctx
      | AnnAssignK id typ (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AnnAssignK id typ k) ctx)
      | AnnAssignK id typ k =>
          set_stmt (AnnAssignK id typ (step_expr ctx.globals fc.scopes k)) ctx
      | ExceptionK err => ctx
      | DoneK => next_stmt ctx
      | ForK id typ (DoneExpr (ArrayV [])) (st::ss) =>
          set_stmt DoneK ctx
      | ForK id typ (DoneExpr (ArrayV vs)) ss =>
          push_loop id typ vs ss ctx
      | ForK id typ (DoneExpr _) _ => raise Error ctx
      | ForK id typ ErrorExpr _ => raise Error ctx
      | ForK id typ ReturnExpr _ => raise Error ctx
      | ForK id typ (LiftCall fn vs k) ss =>
          push_call fn vs
            (set_stmt (ForK id typ k ss) ctx)
      | ForK id typ k ss =>
          set_stmt (ForK id typ (step_expr ctx.globals fc.scopes k) ss) ctx)
End

Definition external_call_def:
  external_call n name args ts =
  case lookup_external_function name ts of
    SOME (params, _, body) =>
    (case bind_arguments params args of
       SOME env =>
       (let fc = initial_function_context env body in
        let ctx = initial_execution_context ts fc in
        let ctx = FUNPOW step_stmt n ctx in
        (case ctx.current_fc.current_stmt
           of ExceptionK (ExternalReturn v) => SOME v
            | _ => NONE))
     | _ => NONE)
  | _ => NONE
End

val () = export_theory();
