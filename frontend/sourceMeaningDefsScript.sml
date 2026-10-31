Theory sourceMeaningDefs
Ancestors
  sourceMeaningValue sourceMeaningConst sourceExprDefs sourceResolve sourceSyntax
  sourceConstValue vyperInterpreter vyperState vyperAST vyperValue
  vyperValueOperation vyperContext alist

(* Source semantic terms are NOT runtime exprs. Constants have already passed
   the mathematical stage. Names denote independently supplied computations;
   runtime operations use the runtime operator algebra only at this stage. *)
Datatype:
  source_meaning = SM_Literal type literal
                 | SM_Name type (string list)
                 | SM_Unary type source_const_unary source_meaning
                 | SM_Binary type source_const_binary source_meaning source_meaning
                 | SM_If type source_meaning source_meaning source_meaning
                 | SM_Revert type source_meaning
                 | SM_Constant type source_const_value
End

Definition source_meaning_type_def:
  source_meaning_type (SM_Literal ty l) = ty /\
  source_meaning_type (SM_Name ty p) = ty /\
  source_meaning_type (SM_Unary ty op e) = ty /\
  source_meaning_type (SM_Binary ty op l r) = ty /\
  source_meaning_type (SM_If ty c l r) = ty /\
  source_meaning_type (SM_Revert ty e) = ty /\
  source_meaning_type (SM_Constant ty sv) = ty
End

Definition source_meaning_stage_def:
  source_meaning_stage scopes table constants original result <=>
    ?resolved. source_resolve_candidate scopes table original = SOME resolved /\
      source_meaning_const constants resolved = result
End

Definition source_meaning_boolean_def:
  source_meaning_boolean op [] = SM_Literal (BaseT BoolT) (BoolL (op = SCB_And)) /\
  source_meaning_boolean op (m::ms) =
    if ms = [] then m else SM_If (BaseT BoolT) m
      (if op = SCB_And then source_meaning_boolean op ms
       else SM_Literal (BaseT BoolT) (BoolL T))
      (if op = SCB_And then SM_Literal (BaseT BoolT) (BoolL F)
       else source_meaning_boolean op ms)
End

(* Independent syntax-directed source rules. These do not mention elaboration,
   runtime code, reification, successful checking, or an emitted AST. Source
   operator legality remains the independent sourceExpr domain check. The
   executable bridge below intentionally starts with scalar replacements. *)
Inductive source_meaning_source:
[constant:]
  source_meaning_stage scopes table constants original (SC_Value sv) /\
  source_const_value_literal sv = SOME lit ==>
  source_meaning_source types scopes table constants ty original (SM_Literal ty lit)
[name:]
  source_expr_path original = SOME names /\
  source_resolve_name scopes table names = SOME (path,SR_Dynamic) /\
  ALOOKUP types path = SOME ty /\
  source_meaning_stage scopes table constants original SC_NotConstant ==>
  source_meaning_source types scopes table constants ty original (SM_Name ty path)
[unary:]
  source_meaning_stage scopes table constants (SX_Unary uop child) SC_NotConstant /\
  source_expr_unary_domain uop ty /\
  source_meaning_source types scopes table constants ty child m ==>
  source_meaning_source types scopes table constants ty (SX_Unary uop child)
    (SM_Unary ty uop m)
[binary:]
  source_meaning_stage scopes table constants (SX_Binary bop left right) SC_NotConstant /\
  (bop <> SCB_LShift /\ bop <> SCB_RShift /\ source_expr_binary_domain bop ty) /\
  source_meaning_source types scopes table constants ty left l /\
  source_meaning_source types scopes table constants ty right r ==>
  source_meaning_source types scopes table constants ty (SX_Binary bop left right)
    (SM_Binary ty bop l r)
[conditional:]
  source_meaning_source types scopes table constants (BaseT BoolT) condition c /\
  source_meaning_source types scopes table constants ty left l /\
  source_meaning_source types scopes table constants ty right r ==>
  source_meaning_source types scopes table constants ty (SX_IfExp condition left right)
    (SM_If ty c l r)
[aggregate:]
  source_meaning_stage scopes table constants original (SC_Value sv) /\
  source_const_value_literal sv = NONE ==>
  source_meaning_source types scopes table constants ty original (SM_Constant ty sv)
[boolean:]
  source_meaning_stage scopes table constants (SX_Boolean op children) SC_NotConstant /\
  2 <= LENGTH children /\
  LIST_REL (source_meaning_source types scopes table constants (BaseT BoolT)) children ms ==>
  source_meaning_source types scopes table constants (BaseT BoolT)
    (SX_Boolean op children) (source_meaning_boolean op ms)
End

(* Effectful dynamic bindings are supported by environment agreement. SM_Revert
   also has direct runtime semantics; its source-call transport is separate. *)

Definition source_meaning_args_def:
  source_meaning_args cx [] = return [] /\
  source_meaning_args cx (m::ms) = do
    tv <- m;
    v <- read_result cx tv;
    vs <- source_meaning_args cx ms;
    return (v::vs)
  od
End

Definition source_meaning_apply_def:
  source_meaning_apply cx ty bt ts ms = do
    type_check (builtin_args_length_ok bt (LENGTH ms)) "Builtin args";
    vs <- source_meaning_args cx ms;
    acc <- get_accounts;
    v <- lift_sum (evaluate_builtin cx acc ty bt ts vs);
    return (Value v)
  od
End

(* Semantic environment: resolved identity -> runtime computation. The theorem
   requires agreement with actual runtime bindings at EVERY threaded state,
   not just at the initial state. Exceptions, effects and pointers are retained. *)
Definition source_meaning_eval_def:
  source_meaning_eval cx meanings (SM_Literal ty l) = return (Value (evaluate_literal l)) /\
  source_meaning_eval cx meanings (SM_Name ty path) = meanings path /\
  source_meaning_eval cx meanings (SM_Unary ty op e) =
    source_meaning_apply cx ty (source_expr_unary op) [source_meaning_type e]
      [source_meaning_eval cx meanings e] /\
  source_meaning_eval cx meanings (SM_Binary ty op l r) =
    source_meaning_apply cx ty (Bop (source_expr_binary op))
      [source_meaning_type l; source_meaning_type r]
      [source_meaning_eval cx meanings l; source_meaning_eval cx meanings r] /\
  source_meaning_eval cx meanings (SM_If ty c l r) = do
    tv <- source_meaning_eval cx meanings c;
    res <- switch_BoolV cx tv (source_meaning_eval cx meanings l) (source_meaning_eval cx meanings r);
    conditional_result cx res
  od /\
  source_meaning_eval cx meanings (SM_Revert ty e) = do
    vs <- source_meaning_args cx [source_meaning_eval cx meanings e];
    type_check (LENGTH vs = 1) "raw_revert args";
    raise (Error (RuntimeError "raw_revert"))
  od /\
  source_meaning_eval cx meanings (SM_Constant ty sv) = do
    v <- lift_option_type (source_meaning_value (get_tenv cx) ty sv) "source constant";
    return (Value v)
  od
End
