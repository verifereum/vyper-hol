open HolKernel boolLib bossLib Parse dep_rewrite
open listTheory alistTheory finite_mapTheory arithmeticTheory
     numposrepTheory stringTheory combinTheory
     cv_typeTheory cv_stdTheory cv_transLib
open vyperAstTheory vfmContextTheory

val () = new_theory "vyperVm";

Definition string_to_num_def:
  string_to_num s = l2n 257 (MAP (SUC o ORD) s)
End

Definition MAP_CHR_o_PRE_def:
  MAP_CHR_o_PRE [] acc = REVERSE acc ∧
  MAP_CHR_o_PRE (x::xs) acc =
  MAP_CHR_o_PRE xs (CHR(PRE x)::acc)
End

val MAP_CHR_o_PRE_pre_def = cv_auto_trans_pre MAP_CHR_o_PRE_def;

Theorem MAP_CHR_o_PRE_pre:
  EVERY ($> 257) v ==>
  MAP_CHR_o_PRE_pre v acc
Proof
  qid_spec_tac`acc` \\ Induct_on`v`
  \\ rw[Once MAP_CHR_o_PRE_pre_def]
QED

Theorem MAP_CHR_o_PRE:
  MAP_CHR_o_PRE ls acc = REVERSE acc ++ (MAP (CHR o PRE) ls)
Proof
  qid_spec_tac`acc` \\ Induct_on`ls`
  \\ rw[MAP_CHR_o_PRE_def]
QED

Definition num_to_string_def:
  num_to_string n =
  if n = 0 then "" else
  MAP (CHR o PRE) (n2l 257 n)
End

Theorem string_to_num_to_string:
  num_to_string (string_to_num s) = s
Proof
  simp[num_to_string_def, string_to_num_def, l2n_eq_0]
  \\ rw[EVERY_MAP]
  >- (
    qmatch_assum_abbrev_tac`EVERY P s`
    \\ `P = K F`
    by (
      rw[Abbr`P`, FUN_EQ_THM]
      \\ DEP_REWRITE_TAC[LESS_MOD]
      \\ rw[SUC_LT]
      \\ qexists_tac`256`
      \\ simp[ORD_BOUND] )
    \\ Cases_on`s` \\ gvs[] )
  \\ DEP_REWRITE_TAC[n2l_l2n]
  \\ simp[l2n_eq_0, EVERY_MAP]
  \\ DEP_REWRITE_TAC[LOG_l2n]
  \\ simp[EVERY_MAP, GREATER_DEF, MAP_TAKE, MAP_MAP_o, o_DEF]
  \\ Cases_on`s = []` \\ gvs[]
  \\ rw[SUC_LT, EVERY_MEM]
  \\ qexists_tac`256`
  \\ simp[ORD_BOUND]
QED

val () = cv_auto_trans string_to_num_def;

val num_to_string_pre_def = cv_auto_trans_pre (
  num_to_string_def
 |> REWRITE_RULE[
      MAP_CHR_o_PRE |> Q.GEN`acc` |> Q.SPEC`[]`
      |> SIMP_RULE std_ss [APPEND, REVERSE_DEF] |> SYM
    ] )

Theorem num_to_string_pre[cv_pre]:
  num_to_string_pre n
Proof
  rw[num_to_string_pre_def]
  \\ irule MAP_CHR_o_PRE_pre
  \\ irule n2l_BOUND
  \\ rw[]
QED

(*
Theorem num_to_string_inj:
  (* this is false because of 0 digits *)
  num_to_string x = num_to_string y ==> x = y
Proof
  simp[num_to_string_def]
  \\ qmatch_goalsub_abbrev_tac`n2l b`
  \\ pop_assum mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\ qid_spec_tac`y`
  \\ qid_spec_tac`x`
  \\ qid_spec_tac`b`
  \\ ho_match_mp_tac n2l_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ gvs[]
  \\ rw[]
  >- rw[Once n2l_def]
  >- rw[Once n2l_def]
  \\ pop_assum mp_tac
  \\ rw[Once n2l_def]
  >- (
    Cases_on`x` \\ gvs[]
    \\ qpat_x_assum`n2l _ _ = _`mp_tac
    \\ rw[Once n2l_def]
    >- ( Cases_on`x0` \\ gvs[] )
    \\ rw[Once n2l_def] )
  \\ pop_assum mp_tac
  \\ simp[Once n2l_def, SimpRHS]
  \\ rw[]
  >- rw[Once n2l_def]
  \\ gs[]
  \\ qspec_then`257`mp_tac DIVISION
  \\ impl_tac >- rw[]
  \\ disch_then(fn th => qspec_then`x`mp_tac th \\ qspec_then`y`mp_tac th)
  \\ ntac 2 strip_tac
  \\ qpat_x_assum`x = _`SUBST1_TAC
  \\ qpat_x_assum`y = _`SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`xd * _ + xm = yd * _ + ym`
  \\ `xd = yd ∧ xm = ym` suffices_by rw[]
  \\ `PRE xm < 256` by (Cases_on`xm` \\ gvs[])
  \\ `PRE ym < 256` by (Cases_on`ym` \\ gvs[])
  \\ gs[]
  \\ Cases_on`xm = 0` >- (
    gvs[Abbr`xm`, MOD_EQ_0_IFF]

  m``PRE 0``

*)

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
  default_value (TupleT ts) = TupleV (default_value_list ts) ∧
  default_value (DynArrayT _ _) = ArrayV [] ∧
  default_value VoidT = VoidV ∧
  default_value (BaseT BoolT) = BoolV F ∧
  default_value (BaseT StringT) = StringV "" ∧
  default_value (BaseT BytesT) = BytesV [] ∧
  default_value_list [] = [] ∧
  default_value_list (t::ts) = default_value t :: default_value_list ts
Termination
  WF_REL_TAC ‘measure
    (λx. case x of INR t => type1_size t | INL t => type_size t)’
End

Theorem default_value_list_MAP:
  default_value_list ls = MAP default_value ls
Proof
  Induct_on`ls` \\ rw[default_value_def]
QED

val () = cv_auto_trans default_value_def;

(*
We don't use this directly to support cv which prefers num keys
Type scope = “:identifier |-> value”;
*)
Type scope = “:num |-> value”;

val from_to_value_thm = cv_typeLib.from_to_thm_for “:value”;
val from_value = from_to_value_thm |> concl |> rator |> rand
val to_value = from_to_value_thm |> concl |> rand

(*
Definition from_scope_def:
  from_scope env = from_fmap ^from_value (env f_o num_to_string)
End

Definition to_scope_def:
  to_scope cv = to_fmap ^to_value cv f_o string_to_num
End

Theorem from_to_scope[cv_from_to]:
  from_to from_scope to_scope
Proof
  mp_tac $ MATCH_MP from_to_fmap from_to_value_thm
  \\ rw[from_to_def, from_scope_def, to_scope_def]
  \\ DEP_REWRITE_TAC[f_o_ASSOC]
  \\ rw[EQ_IMP_THM]
  >- cheat
  >- metis_tac[string_to_num_to_string]
  \\ irule (iffLR fmap_EQ_THM)
  \\ DEP_REWRITE_TAC[FDOM_f_o]
  \\ simp[o_DEF, string_to_num_to_string]
  \\ rw[]
  \\ DEP_REWRITE_TAC[FAPPLY_f_o]
  \\ simp[]
QED
*)

Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME v => SOME v
End

(*
TODO: somehow rework to use num_maps?
val () = cv_auto_trans lookup_scopes_def;
*)

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
  | ErrorExpr string
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
  | ErrorTgt string
End

Datatype:
  exception
  = RaiseException string
  | AssertException string
  | Error string
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

val () = cv_auto_trans evaluate_literal_def;

Definition evaluate_cmp_def:
  evaluate_cmp Eq    (StringV s1) (StringV s2) = DoneExpr (BoolV (s1 = s2)) ∧
  evaluate_cmp Eq    (IntV i1)    (IntV i2)    = DoneExpr (BoolV (i1 = i2)) ∧
  evaluate_cmp NotEq (StringV s1) (StringV s2) = DoneExpr (BoolV (s1 ≠ s2)) ∧
  evaluate_cmp NotEq (IntV i1)    (IntV i2)    = DoneExpr (BoolV (i1 ≠ i2)) ∧
  evaluate_cmp _ _ _ = ErrorExpr "cmp"
End

val () = cv_auto_trans evaluate_cmp_def;

Definition evaluate_binop_def:
  evaluate_binop Add (IntV i1) (IntV i2) = DoneExpr (IntV (i1 + i2)) ∧
  evaluate_binop Sub (IntV i1) (IntV i2) = DoneExpr (IntV (i1 - i2)) ∧
  evaluate_binop (_: operator) _ _ = ErrorExpr "binop"
End

val () = cv_auto_trans evaluate_binop_def;

Definition extract_elements_def:
  extract_elements (ArrayV vs) = SOME vs ∧
  extract_elements (TupleV vs) = SOME vs ∧
  extract_elements _ = NONE
End

val () = cv_auto_trans extract_elements_def;

Definition replace_elements_def:
  replace_elements (ArrayV _) vs = SOME (ArrayV vs) ∧
  replace_elements (TupleV _) vs = SOME (TupleV vs) ∧
  replace_elements _ _ = NONE
End

val () = cv_auto_trans replace_elements_def;

Definition integer_index_def:
  integer_index vs i =
   if Num i < LENGTH vs then
     SOME $ if 0 ≤ i then Num i else LENGTH vs - Num i
   else NONE
End

val () = cv_auto_trans integer_index_def;

Definition evaluate_subscript_def:
  evaluate_subscript av (IntV i) =
  (case extract_elements av of SOME vs =>
    (case integer_index vs i of SOME j => DoneExpr (EL j vs)
     | _ => ErrorExpr "integer_index")
   | _ => ErrorExpr "extract_elements") ∧
  evaluate_subscript _ _ = ErrorExpr "evaluate_subscript"
End

val evaluate_subscript_pre_def = cv_auto_trans_pre evaluate_subscript_def;

Theorem evaluate_subscript_pre[cv_pre]:
  evaluate_subscript_pre av v
Proof
  rw[evaluate_subscript_pre_def, integer_index_def]
  \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ v0`
  \\ Cases_on`v0` \\ gs[]
QED

Definition evaluate_attribute_def:
  evaluate_attribute (StructV kvs) id =
  (case ALOOKUP kvs id of SOME v => DoneExpr v
   | _ => ErrorExpr "attribute") ∧
  evaluate_attribute _ _ = ErrorExpr "evaluate_attribute"
End

val () = cv_auto_trans evaluate_attribute_def;

Definition step_expr_def:
  step_expr gbs env (StartExpr (Literal l)) =
    DoneExpr (evaluate_literal l) ∧
  step_expr gbs env (StartExpr (ArrayLit [])) =
    DoneExpr (ArrayV []) ∧
  step_expr gbs env (StartExpr (ArrayLit (e::es))) =
    ArrayLitK [] (StartExpr e) es ∧
  step_expr gbs env (StartExpr (Name id)) =
    (case lookup_scopes (string_to_num id) env
     of SOME v => DoneExpr v
      | _ => ErrorExpr "lookup_scopes") ∧
  step_expr gbs env (StartExpr (GlobalName id)) =
    (case FLOOKUP gbs (string_to_num id)
     of SOME (Value v) => DoneExpr v
      | _ => ErrorExpr "lookup gbs") ∧
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
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v1 => (case v1 of BoolV b => StartExpr (if b then e2 else e3)
                               | _ => ErrorExpr "IfExpK value")
    | LiftCall id vs k => LiftCall id vs (IfExpK k e2 e3)
    | k => IfExpK k e2 e3) ∧
  step_expr gbs env (ArrayLitK vs k es) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v =>
        (case es of (e::es) => ArrayLitK (SNOC v vs) (StartExpr e) es
                  | [] => DoneExpr (ArrayV (SNOC v vs)))
    | LiftCall id as k => LiftCall id as (ArrayLitK vs k es)
    | k => ArrayLitK vs k es) ∧
  step_expr gbs env (SubscriptK1 k e) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v => SubscriptK2 v (StartExpr e)
    | LiftCall id vs k => LiftCall id vs (SubscriptK1 k e)
    | k => SubscriptK1 k e) ∧
  step_expr gbs env (SubscriptK2 v1 k) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v2 => evaluate_subscript v1 v2
    | LiftCall id vs k => LiftCall id vs (SubscriptK2 v1 k)
    | k => SubscriptK2 v1 k) ∧
  step_expr gbs env (AttributeK k id) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v => evaluate_attribute v id
    | LiftCall id vs k => LiftCall id vs (AttributeK k id)
    | k => AttributeK k id) ∧
  step_expr gbs env (CompareK1 k cmp e2) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v1 => CompareK2 v1 cmp (StartExpr e2)
    | LiftCall id vs k => LiftCall id vs (CompareK1 k cmp e2)
    | k => CompareK1 k cmp e2) ∧
  step_expr gbs env (CompareK2 v1 cmp k) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v2 => evaluate_cmp cmp v1 v2
    | LiftCall id vs k => LiftCall id vs (CompareK2 v1 cmp k)
    | k => CompareK2 v1 cmp k) ∧
  step_expr gbs env (BinOpK1 k bop e2) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v1 => BinOpK2 v1 bop (StartExpr e2)
    | LiftCall id vs k => LiftCall id vs (BinOpK1 k bop e2)
    | k => BinOpK1 k bop e2) ∧
  step_expr gbs env (BinOpK2 v1 bop k) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v2 => evaluate_binop bop v1 v2
    | LiftCall id vs k => LiftCall id vs (BinOpK2 v1 bop k)
    | k => BinOpK2 v1 bop k) ∧
  step_expr gbs env (CallK id vs k es) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v =>
        (case es of (e::es) => CallK id (SNOC v vs) (StartExpr e) es
                  | [] => LiftCall id (SNOC v vs) ReturnExpr)
    | LiftCall id vs k => LiftCall id vs (CallK id vs k es)
    | k => CallK id vs k es) ∧
  step_expr gbs env (LiftCall id vs k) = LiftCall id vs k ∧
  step_expr gbs env (DoneExpr v) = DoneExpr v ∧
  step_expr gbs env ReturnExpr = ReturnExpr ∧
  step_expr gbs env (ErrorExpr msg) = ErrorExpr msg
End

val () = cv_auto_trans step_expr_def;

Datatype:
  loop_info = <|
    loop_var: (* identifier *) num
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
  ; globals: (* identifier *) num |-> toplevel_value
  ; contract: toplevel list
  |>
End

Definition initial_function_context_def:
  initial_function_context args ss = <|
    scopes := [args]
  ; current_stmt := (case ss of s::_ => StartK s
                        | _ => ExceptionK (Error "initial_function_context"))
  ; remaining_stmts := TL ss
  ; loop := NONE
  |>
End

val () = cv_auto_trans initial_function_context_def;

(* TODO: assumes unique identifiers, but should check? *)
Definition initial_globals_def:
  initial_globals [] = FEMPTY ∧
  initial_globals (VariableDecl id typ _ Storage :: ts) =
  initial_globals ts |+ (string_to_num id, Value $ default_value typ) ∧
  initial_globals (VariableDecl id typ _ Transient :: ts) =
  initial_globals ts |+ (string_to_num id, Value $ default_value typ) ∧
  (* TODO: handle Constants and  Immutables *)
  initial_globals (t :: ts) = initial_globals ts
  (* TODO: hashmap toplevels *)
End

val () = cv_auto_trans initial_globals_def;

Definition initial_execution_context_def:
  initial_execution_context ts fc = <|
    current_fc := fc
  ; call_stack := []
  ; globals := initial_globals ts
  ; contract := ts
  |>
End

val () = cv_auto_trans initial_execution_context_def;

Definition raise_def:
  raise err ctx = ctx with current_fc updated_by
    (λfc. fc with current_stmt := ExceptionK err)
End

val () = cv_auto_trans raise_def;

Definition push_scope_def:
  push_scope ctx =
    ctx with current_fc updated_by (λfc. fc with scopes updated_by CONS FEMPTY)
End

val () = cv_auto_trans push_scope_def;

Definition pop_scope_def:
  pop_scope ctx =
  case ctx.current_fc.scopes
    of [] => raise (Error "pop_scope") ctx
     | (_::rest) => ctx with current_fc updated_by (λfc. fc with scopes := rest)
End

val () = cv_auto_trans pop_scope_def;

Definition new_variable_def:
  new_variable id typ ctx =
  case ctx.current_fc.scopes
    of [] => raise (Error "new_variable") ctx
     | env::rest =>
         if id ∈ FDOM env then raise (Error "var exists") ctx
         else ctx with current_fc updated_by
           (λfc. fc with scopes := (env |+ (id, default_value typ))::rest)
End

val () = cv_auto_trans (REWRITE_RULE[TO_FLOOKUP]new_variable_def);

Definition find_containing_scope_def:
  find_containing_scope id [] = NONE : containing_scope option ∧
  find_containing_scope id (env::rest) =
  if id ∈ FDOM env then SOME ([], env, rest)
  else OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
End

val () = cv_auto_trans (REWRITE_RULE[TO_FLOOKUP]find_containing_scope_def);

Definition step_base_target_def:
  step_base_target gbs env (StartBaseTgt (NameTarget id)) =
    (case find_containing_scope (string_to_num id) env
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
     | ErrorExpr msg => NONE
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
    | _ => NONE) ∧
  step_base_target gbs env (LiftCallBaseTgt fn vs k) =
    SOME $ LiftCallBaseTgt fn vs k ∧
  step_base_target gbs env (DoneBaseTgt l s) =
    SOME $ DoneBaseTgt l s
End

val () = cv_auto_trans step_base_target_def;

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
    | ErrorTgt msg => ErrorTgt msg
    | k => TupleTargetK vs k ts) ∧
  step_target gbs env (BaseTargetK k) =
  (case step_base_target gbs env k
   of SOME (DoneBaseTgt l s) => DoneTgt $ BaseTargetV l s
    | SOME (LiftCallBaseTgt fn vs k) => LiftCallTgt fn vs (BaseTargetK k)
    | SOME k => BaseTargetK k
    | _ => ErrorTgt "step_base_target") ∧
  step_target gbs env (LiftCallTgt fn vs k) = LiftCallTgt fn vs k ∧
  step_target gbs env (DoneTgt v) = DoneTgt v ∧
  step_target gbs env (ErrorTgt msg) = ErrorTgt msg
End

val () = cv_auto_trans step_target_def;

Definition set_variable_def:
  set_variable id v ctx =
  case find_containing_scope id ctx.current_fc.scopes
    of NONE => raise (Error "find_containing_scope") ctx
     | SOME (pre, env, rest) =>
         (* check that v has same type as current value here ? *)
         ctx with current_fc updated_by
           (λfc. fc with scopes := pre ++ (env |+ (id, v))::rest)
End

val () = cv_auto_trans set_variable_def;

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

val assign_subscripts_pre_def = cv_auto_trans_pre assign_subscripts_def;

Theorem assign_subscripts_pre[cv_pre]:
  !a b c. assign_subscripts_pre a b c
Proof
  ho_match_mp_tac assign_subscripts_ind
  \\ rw[Once assign_subscripts_pre_def]
  \\ rw[Once assign_subscripts_pre_def]
  \\ gvs[integer_index_def] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ v0`
  \\ Cases_on`v0` \\ gs[]
QED

Definition assign_target_def:
  assign_target (BaseTargetV (ScopedVar (pre,env,rest) id) is) v ctx =
    (let nid = string_to_num id in
    (case FLOOKUP env nid of SOME a =>
     (case assign_subscripts a is v of SOME a' =>
        ctx with current_fc updated_by
          (λfc. fc with scopes := pre ++ (env |+ (nid, a'))::rest)
      | _ => raise (Error "assign_subscripts ScopedVar") ctx)
     | _ => raise (Error "assign_target lookup") ctx)) ∧
  assign_target (BaseTargetV (Global id) is) v ctx =
  (let nid = string_to_num id in
  (* TODO: add assignment to hashmaps *)
  (case FLOOKUP ctx.globals nid of SOME (Value a) =>
   (case assign_subscripts a is v of SOME a' =>
     ctx with globals := ctx.globals |+ (nid, Value a')
    | _ => raise (Error "assign_subscripts Global") ctx)
   | _ => raise (Error "assign_target globals lookup") ctx)) ∧
  assign_target _ _ ctx = raise (Error "TODO: TupleTargetV") ctx
End

val () = cv_auto_trans assign_target_def;

(* TODO: check types? *)
Definition bind_arguments_def:
  bind_arguments ([]: argument list) [] = SOME (FEMPTY: scope) ∧
  bind_arguments ((id, typ)::params) (v::vs) =
    OPTION_MAP (λm. m |+ (string_to_num id, v)) (bind_arguments params vs) ∧
  bind_arguments _ _ = NONE
End

val () = cv_auto_trans bind_arguments_def;

Definition lookup_external_function_def:
  lookup_external_function name [] = NONE ∧
  lookup_external_function name (FunctionDef id External args ret body :: ts) =
  (if id = name then SOME (args, ret, body)
   else lookup_external_function name ts) ∧
  lookup_external_function name (_ :: ts) =
    lookup_external_function name ts
End

val () = cv_auto_trans lookup_external_function_def;

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
     | _ => raise (Error "bind_arguments") ctx)
  | _ => raise (Error "lookup_external_function") ctx
End

val () = cv_auto_trans push_call_def;

Definition update_current_stmt_def:
  update_current_statement st ctx =
  ctx with current_fc updated_by
    (λfc. fc with current_stmt := st)
End

val () = cv_auto_trans update_current_stmt_def;

Definition return_expr_def:
  return_expr v (StartExpr _) = ErrorExpr "return StartExpr" ∧
  return_expr v (IfExpK k e1 e2) = IfExpK (return_expr v k) e1 e2  ∧
  return_expr v (ArrayLitK vs k es) = ArrayLitK vs (return_expr v k) es ∧
  return_expr v (SubscriptK1 k e) = SubscriptK1 (return_expr v k) e ∧
  return_expr v (SubscriptK2 w k) = SubscriptK2 w (return_expr v k) ∧
  return_expr v (AttributeK k id) = AttributeK (return_expr v k) id ∧
  return_expr v (CompareK1 k cmp e) = CompareK1 (return_expr v k) cmp e ∧
  return_expr v (CompareK2 w cmp k) = CompareK2 w cmp (return_expr v k) ∧
  return_expr v (BinOpK1 k bop e) = BinOpK1 (return_expr v k) bop e ∧
  return_expr v (BinOpK2 w bop k) = BinOpK2 w bop (return_expr v k) ∧
  return_expr v (CallK id vs k es) = CallK id vs (return_expr v k) es ∧
  return_expr v (LiftCall fn vs k) = LiftCall fn vs (return_expr v k) ∧
  return_expr v (DoneExpr _) = ErrorExpr "return DoneExpr" ∧
  return_expr v ReturnExpr = DoneExpr v ∧
  return_expr v (ErrorExpr msg) = ErrorExpr msg
End

val () = cv_auto_trans return_expr_def;

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

val () = cv_auto_trans return_base_tgt_def;

Definition return_tgt_def:
  return_tgt v (StartTgt _) = ErrorTgt "return StartTgt" ∧
  return_tgt v (TupleTargetK vs k as) =
    TupleTargetK vs (return_tgt v k) as ∧
  return_tgt v (BaseTargetK t) =
    (case return_base_tgt v t of NONE => ErrorTgt "return_base_tgt"
        | SOME t => BaseTargetK t) ∧
  return_tgt v (LiftCallTgt fn vs k) =
    LiftCallTgt fn vs (return_tgt v k) ∧
  return_tgt v (DoneTgt _) = ErrorTgt "return DoneTgt" ∧
  return_tgt v (ErrorTgt msg) = ErrorTgt msg
End

val () = cv_auto_trans return_tgt_def;

Definition return_def:
  return v (ForK id typ k ss) = ForK id typ (return_expr v k) ss ∧
  return v (IfK k s1 s2) = IfK (return_expr v k) s1 s2 ∧
  return v (AssertK k s) = AssertK (return_expr v k) s ∧
  return v (ReturnSomeK k) = ReturnSomeK (return_expr v k) ∧
  return v (AssignK1 t e) = AssignK1 (return_tgt v t) e ∧
  return v (AssignK2 a k) = AssignK2 a (return_expr v k) ∧
  return v (AugAssignK id op k) = AugAssignK id op (return_expr v k) ∧
  return v (AnnAssignK id typ k) = AnnAssignK id typ (return_expr v k) ∧
  return v (StartK _) = ExceptionK (Error "return StartK") ∧
  return v (DoneK) = ExceptionK (Error "return DoneK") ∧
  return v (ExceptionK err) = ExceptionK (Error "return ExceptionK")
End

val () = cv_auto_trans return_def;

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

val pop_call_pre_def = cv_auto_trans_pre pop_call_def;

Theorem pop_call_pre[cv_pre]:
  ∀v ctx. pop_call_pre v ctx
Proof
  ho_match_mp_tac pop_call_ind
  \\ rw[]
  \\ rw[Once pop_call_pre_def]
  \\ fs[]
  \\ qmatch_assum_abbrev_tac`pop_call_pre v c1`
  \\ qmatch_goalsub_abbrev_tac`pop_call_pre v c2`
  \\ `c1 = c2` suffices_by (rw[] \\ fs[])
  \\ rw[Abbr`c1`, Abbr`c2`]
  \\ CASE_TAC
  \\ rw[ theorem"execution_context_component_equality"]
QED

Definition set_stmt_def:
  set_stmt k ctx =
    ctx with current_fc updated_by (λfc. fc with current_stmt := k)
End

val () = cv_auto_trans set_stmt_def;

Definition exception_raised_def:
  exception_raised ctx <=>
  case ctx.current_fc.current_stmt of ExceptionK _ => T | _ => F
End

val () = cv_auto_trans exception_raised_def;

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
  push_loop _ _ _ _ ctx = raise (Error "push_loop") ctx
End

val () = cv_auto_trans push_loop_def;

Definition pop_loop_def:
  pop_loop ctx =
  case ctx.call_stack of
     | [] => raise (Error "pop_loop") ctx
     | fc::fcs => ctx with <|
         current_fc := (fc with <|
           current_stmt := DoneK (* check it was ForK? *)
         ; scopes := ctx.current_fc.scopes
             (* TODO: is this a reason to maybe not have a loop context?  *)
         |>)
       ; call_stack := fcs |>
End

val () = cv_auto_trans pop_loop_def;

Definition next_iteration_def:
  next_iteration li ctx =
  case li.remaining_values of [] => pop_loop ctx
     | v::vs => ctx with current_fc updated_by (λfc.
        fc with <| scopes updated_by CONS (FEMPTY |+ (li.loop_var, v))
                 ; current_stmt := StartK li.loop_first_stmt
                 ; remaining_stmts := li.loop_rest_stmts
                 ; loop := SOME (li with remaining_values := vs) |>)
End

val () = cv_auto_trans next_iteration_def;

Definition continue_loop_def:
  continue_loop ctx =
  case ctx.current_fc.loop of SOME li => (
    let ctx = pop_scope ctx in
      if exception_raised ctx then ctx else
        next_iteration li ctx
  ) | _ => raise (Error "continue_loop") ctx
End

val () = cv_auto_trans continue_loop_def;

Definition break_loop_def:
  break_loop ctx =
  case ctx.current_fc.loop of SOME li => (
    let ctx = pop_scope ctx in
      if exception_raised ctx then ctx else
        pop_loop ctx
  ) | _ => raise (Error "break_loop") ctx
End

val () = cv_auto_trans break_loop_def;

Definition next_stmt_def:
  next_stmt ctx =
  case ctx.current_fc.remaining_stmts of s::ss =>
    ctx with current_fc updated_by (λfc.
      fc with <| current_stmt := StartK s
               ; remaining_stmts := ss |>)
  | _ => (case ctx.current_fc.loop
            of NONE => pop_call VoidV ctx
             | SOME li =>
                 let ctx = pop_scope ctx in
                   if exception_raised ctx then ctx
                   else next_iteration li ctx)
End

val () = cv_auto_trans next_stmt_def;

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
          | _ => raise (Error "IfK body") ctx)
      | IfK (DoneExpr _) _ _ => raise (Error "IfK DoneExpr") ctx
      | IfK (ErrorExpr msg) _ _ => raise (Error ("IfK " ++ msg)) ctx
      | IfK ReturnExpr _ _ => raise (Error "IfK ReturnExpr") ctx
      | IfK (LiftCall fn vs k) s1 s2 =>
          push_call fn vs
            (set_stmt (IfK k s1 s2) ctx)
      | IfK k s1 s2 =>
          set_stmt
            (IfK (step_expr ctx.globals fc.scopes k) s1 s2) ctx
      | AssertK (DoneExpr (BoolV b)) s => (
          if b then set_stmt DoneK ctx
          else raise (AssertException s) ctx)
      | AssertK (DoneExpr _) _ => raise (Error "AssertK DoneExpr") ctx
      | AssertK (ErrorExpr msg) _ => raise (Error "AssertK ErrorExpr") ctx
      | AssertK ReturnExpr _ => raise (Error "AssertK ReturnExpr") ctx
      | AssertK (LiftCall fn vs k) s =>
          push_call fn vs
            (set_stmt (AssertK k s) ctx)
      | AssertK k s =>
          set_stmt (AssertK (step_expr ctx.globals fc.scopes k) s) ctx
      | ReturnSomeK (DoneExpr v) => pop_call v ctx
      | ReturnSomeK (ErrorExpr msg) => raise (Error "ReturnSomeK err") ctx
      | ReturnSomeK ReturnExpr => raise (Error "ReturnSomeK ReturnExpr") ctx
      | ReturnSomeK (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (ReturnSomeK k) ctx)
      | ReturnSomeK k =>
          set_stmt
            (ReturnSomeK (step_expr ctx.globals fc.scopes k)) ctx
      | AssignK1 (DoneTgt av) e =>
          set_stmt (AssignK2 av (StartExpr e)) ctx
      | AssignK1 (ErrorTgt msg) e => raise (Error "AssignK1 err") ctx
      | AssignK1 (LiftCallTgt fn vs tk) e =>
          push_call fn vs
            (set_stmt (AssignK1 tk e) ctx)
      | AssignK1 tk e =>
          set_stmt
            (AssignK1 (step_target ctx.globals fc.scopes tk) e) ctx
      | AssignK2 tv (DoneExpr v) =>
          set_stmt DoneK (assign_target tv v ctx)
      | AssignK2 tv (ErrorExpr msg) => raise (Error "AssignK2 err") ctx
      | AssignK2 tv ReturnExpr => raise (Error "AssignK2 ReturnExpr") ctx
      | AssignK2 tv (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AssignK2 tv k) ctx)
      | AssignK2 tv k =>
          set_stmt
            (AssignK2 tv (step_expr ctx.globals fc.scopes k)) ctx
      | AugAssignK id bop (DoneExpr v2) =>
        (let nid = string_to_num id in
        (case lookup_scopes nid fc.scopes
           of NONE => raise (Error "AugAssignK lookup_scopes") ctx
            | SOME v1 =>
              (case evaluate_binop bop v1 v2
                 of DoneExpr v => set_stmt DoneK (set_variable nid v ctx)
                  | _ => raise (Error "AugAssignK bop") ctx)))
      | AugAssignK id bop (ErrorExpr msg) => raise (Error "AugAssignK err") ctx
      | AugAssignK id bop ReturnExpr => raise (Error "AugAssignK ReturnExpr") ctx
      | AugAssignK id bop (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AugAssignK id bop k) ctx)
      | AugAssignK id bop k =>
          set_stmt
            (AugAssignK id bop (step_expr ctx.globals fc.scopes k)) ctx
      | AnnAssignK id typ (DoneExpr v) => (
          let nid = string_to_num id in
          let ctx = new_variable nid typ ctx in
            if exception_raised ctx then ctx else
              set_stmt DoneK (set_variable nid v ctx))
      | AnnAssignK id typ (ErrorExpr msg) => raise (Error "AnnAssignK err") ctx
      | AnnAssignK id typ ReturnExpr => raise (Error "AnnAssignK ReturnExpr") ctx
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
          push_loop (string_to_num id) typ vs ss ctx
      | ForK id typ (DoneExpr _) _ => raise (Error "ForK DoneExpr") ctx
      | ForK id typ (ErrorExpr msg) _ => raise (Error "ForK err") ctx
      | ForK id typ ReturnExpr _ => raise (Error "ForK ReturnExpr") ctx
      | ForK id typ (LiftCall fn vs k) ss =>
          push_call fn vs
            (set_stmt (ForK id typ k ss) ctx)
      | ForK id typ k ss =>
          set_stmt (ForK id typ (step_expr ctx.globals fc.scopes k) ss) ctx)
End

val () = cv_auto_trans step_stmt_def;

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
           of ExceptionK (ExternalReturn v) => INL v
            | ExceptionK (Error msg) => INR msg
            | _ => INR "current_stmt"))
     | _ => INR "external bind_arguments")
  | _ => INR "external lookup"
End

val () = cv_auto_trans external_call_def;

val () = export_theory();
