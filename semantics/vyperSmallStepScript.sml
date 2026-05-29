Theory vyperSmallStep
Ancestors
  arithmetic combin pair list While
  vyperMisc vyperValue vyperContext vyperState vyperInterpreter vyperABI
Libs
  cv_transLib

(*
  plan for cps version:
  - define the same functions as in evaluate_def, but with an additional
    continuation argument. make the state argument explicit.
  - whenever there's a recursive call, make it a tail call and store anything
    required for the remainder on top of the given continuation
  - whenever there's a return (or raise), call an "apply" function (these are
    additional compared to evaluate_def) that applies the continuation to the
    result (there will be a kind of apply function for each kind of result)
  - applying a continuation to a result that it doesn't expect is an error: find
    the results it could expect by looking at where it was created
*)

Datatype:
  eval_continuation
  = ReturnK eval_continuation
  | AssertK assert_reason eval_continuation
  | RaiseK eval_continuation
  | LogK nsid eval_continuation
  | PopK eval_continuation
  | AppendK expr eval_continuation
  | AppendK1 base_target_value eval_continuation
  | AnnAssignK identifier type_value eval_continuation
  | AssignK expr eval_continuation
  | AssignK1 assignment_value eval_continuation
  | AugAssignK type binop expr eval_continuation
  | AugAssignK1 type base_target_value binop eval_continuation
  | IfK (stmt list) (stmt list) eval_continuation
  | IfK1 toplevel_value (stmt list) (stmt list) eval_continuation
  | IfK2 eval_continuation
  | ForK identifier type_value num (stmt list) eval_continuation
  | ForK1 type_value num (stmt list) (value list) eval_continuation
  | ExprK eval_continuation
  | StmtsK (stmt list) eval_continuation
  | ArrayK type eval_continuation
  | RangeK1 expr eval_continuation
  | RangeK2 value eval_continuation
  | BaseTargetK eval_continuation
  | TupleTargetK eval_continuation
  | TargetsK (assignment_target list) eval_continuation
  | TargetsK1 assignment_value eval_continuation
  | AttributeTargetK identifier eval_continuation
  | SubscriptTargetK expr eval_continuation
  | SubscriptTargetK1 base_target_value eval_continuation
  | IfExpK expr expr eval_continuation
  | StructLitK (identifier list) eval_continuation
  | SubscriptK type expr eval_continuation
  | SubscriptK1 type toplevel_value eval_continuation
  | AttributeK identifier eval_continuation
  | BuiltinK type builtin eval_continuation
  | LenK eval_continuation
  | TypeBuiltinK type_builtin type eval_continuation
  | CallSendK eval_continuation
  | ExtCallK bool identifier (type list) type (expr option) eval_continuation
  (* Chain interaction builtin continuations *)
  | RawCallK type raw_call_flags eval_continuation
  | RawLogK eval_continuation
  | RawRevertK eval_continuation
  | SelfDestructK eval_continuation
  | CreateK type create_kind bool eval_continuation
  | IntCallK (num |-> type_args) (num option # identifier) ((identifier # type) list) (expr list) type (stmt list) bool function_mutability eval_continuation
  | IntCallK1 (num |-> type_args) (num option # identifier) ((identifier # type) list) (value list) type (stmt list) bool function_mutability eval_continuation
  | IntCallK2 (scope list) type_value bool bool eval_continuation
  | ExprsK (expr list) eval_continuation
  | ExprsK1 value eval_continuation
  | DoneK
End

Datatype:
  apply_base_continuation
  = Apply
  | ApplyExc exception
  | ApplyTarget assignment_value
  | ApplyTargets (assignment_value list)
  | ApplyBaseTarget base_target_value
  | ApplyTv toplevel_value
  | ApplyVal value
  | ApplyVals (value list)
End

Datatype:
  apply_continuation
  = AK evaluation_context apply_base_continuation
       evaluation_state eval_continuation
End

Definition liftk_def:
  liftk cx a (INL x, st) = AK cx (a x) (st:evaluation_state) ∧
  liftk cx a (INR (ex:exception), st) = AK cx (ApplyExc ex) st
End

val liftk1 = oneline liftk_def;

Definition no_recursion_def:
  no_recursion (src_fn : num option # identifier) stk ⇔ ¬MEM src_fn stk
End

val () = cv_auto_trans no_recursion_def;

Definition eval_base_target_cps_def:
  eval_base_target_cps cx (NameTarget id) st k =
    (let r = do
        sc <- get_scopes;
        n <<- string_to_num id;
        type_check (IS_SOME (lookup_scopes n sc)) "NameTarget not in scope";
        return $ (ScopedVar id, []) od st in
     liftk cx ApplyBaseTarget r k) ∧
  eval_base_target_cps cx (BareGlobalNameTarget id) st k =
    (let r = do
        imms <- get_immutables cx (current_module cx);
        n <<- string_to_num id;
        ts <- lift_option_type
                (get_module_code cx (current_module cx))
                "BareGlobalNameTarget get_module_code";
        type_check (is_immutable_decl n ts) "assign to constant";
        type_check (IS_SOME (FLOOKUP imms n)) "BareGlobalNameTarget not found";
        return $ (ImmutableVar id, []) od st in
     liftk cx ApplyBaseTarget r k) ∧
  eval_base_target_cps cx (TopLevelNameTarget (src_id_opt, id)) st k =
    AK cx (ApplyBaseTarget (TopLevelVar src_id_opt id, [])) st k ∧
  eval_base_target_cps cx (AttributeTarget t id) st k =
    eval_base_target_cps cx t st (AttributeTargetK id k) ∧
  eval_base_target_cps cx (SubscriptTarget t e) st k =
    eval_base_target_cps cx t st (SubscriptTargetK e k)
End

val () = eval_base_target_cps_def
  |> SRULE [bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR, lift_option_def, lift_option_type_def, lift_option_type_def,
            prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, liftk1]
  |> cv_auto_trans;

Definition eval_expr_cps_def:
  eval_expr_cps cx1 (Name _ id) st k =
    liftk cx1 ApplyTv
      (do env <- get_scopes;
          n <<- string_to_num id;
          v <- lift_option_type (lookup_scopes_val n env) "Name not in scope";
          return $ Value v od st) k ∧
  eval_expr_cps cx1 (BareGlobalName _ id) st k =
    liftk cx1 ApplyTv
      (do imms <- get_immutables cx1 (current_module cx1);
          n <<- string_to_num id;
          tvv <- lift_option_type (FLOOKUP imms n) "BareGlobalName not found";
          return $ Value (SND tvv) od st) k ∧
  eval_expr_cps cx2 (TopLevelName _ (src_id_opt, id)) st k =
    liftk cx2 ApplyTv (lookup_global cx2 src_id_opt (string_to_num id) st) k ∧
  eval_expr_cps cx2 (FlagMember _ nsid mid) st k =
    liftk cx2 ApplyTv (lookup_flag_mem cx2 nsid mid st) k ∧
  eval_expr_cps cx3 (IfExp _ e1 e2 e3) st k =
    eval_expr_cps cx3 e1 st (IfExpK e2 e3 k) ∧
  eval_expr_cps cx4 (Literal _ l) st k =
    AK cx4 (ApplyTv (Value $ evaluate_literal l)) st k ∧
  eval_expr_cps cx5 (StructLit _ (src_id_opt, id) kes) st k =
    eval_exprs_cps cx5 (MAP SND kes) st (StructLitK (MAP FST kes) k) ∧
  eval_expr_cps cx6 (Subscript _ e1 e2) st k =
    eval_expr_cps cx6 e1 st (SubscriptK (expr_type e1) e2 k) ∧
  eval_expr_cps cx7 (Attribute _ e id) st k =
    eval_expr_cps cx7 e st (AttributeK id k) ∧
  eval_expr_cps cx8 (Builtin ty bt es) st k =
    (case type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st of
       (INR ex, st) => AK cx8 (ApplyExc ex) st k
     | (INL (), st) => if bt = Len then eval_expr_cps cx8 (HD es) st (LenK k)
                       else eval_exprs_cps cx8 es st (BuiltinK ty bt k)) ∧
  eval_expr_cps cx8 (Pop _ bt) st k =
    eval_base_target_cps cx8 bt st (PopK k) ∧
  eval_expr_cps cx8 (TypeBuiltin _ tb typ es) st k =
    (case type_check (type_builtin_args_length_ok tb (LENGTH es))
            "TypeBuiltin args" st of
        (INR ex, st) => AK cx8 (ApplyExc ex) st k
      | (INL tv, st) => eval_exprs_cps cx8 es st (TypeBuiltinK tb typ k)) ∧
  eval_expr_cps cx9 (Call _ Send es _) st k =
    (case type_check (LENGTH es = 2) "Send args" st of
       (INR ex, st) => AK cx9 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx9 es st (CallSendK k)) ∧
  eval_expr_cps cx10 (Call _ (ExtCall is_static (func_name, arg_types, ret_type)) es drv) st k =
    eval_exprs_cps cx10 es st (ExtCallK is_static func_name arg_types ret_type drv k) ∧
  (* Chain interaction builtins *)
  eval_expr_cps cx10 (Call ty (RawCallTarget flags) es _) st k =
    eval_exprs_cps cx10 es st (RawCallK ty flags k) ∧
  eval_expr_cps cx10 (Call _ RawLog es _) st k =
    eval_exprs_cps cx10 es st (RawLogK k) ∧
  eval_expr_cps cx10 (Call _ RawRevert es _) st k =
    eval_exprs_cps cx10 es st (RawRevertK k) ∧
  eval_expr_cps cx10 (Call _ SelfDestructTarget es _) st k =
    eval_exprs_cps cx10 es st (SelfDestructK k) ∧
  eval_expr_cps cx10 (Call ty (CreateTarget kind rof) es _) st k =
    eval_exprs_cps cx10 es st (CreateK ty kind rof k) ∧
  eval_expr_cps cx10 (Call _ (IntCall (ns, fn)) es _) st k =
    (case do
      check (no_recursion (ns, fn) cx10.stk) "recursion";
      ts <- lift_option_type (get_module_code cx10 ns) "IntCall get_module_code";
      tup <- lift_option_type (lookup_callable_function cx10.in_deploy fn ts) "IntCall lookup_function";
      (* tup = (mut, nr, args, dflts, ret, body) *)
      mut <<- FST tup; stup <<- SND tup; nr <<- FST stup; stup2 <<- SND stup;
      args <<- FST stup2; sstup <<- SND stup2;
      dflts <<- FST sstup; sstup2 <<- SND sstup;
      ret <<- FST $ sstup2; body <<- SND $ sstup2;
      type_check (LENGTH es ≤ LENGTH args ∧
           LENGTH args - LENGTH es ≤ LENGTH dflts) "IntCall args length";
      (* Use combined type env (may reference types from other modules) *)
      all_tenv <<- get_tenv cx10;
      return (all_tenv, args, dflts, ret, body, nr, mut) od st
     of (INR ex, st) => AK cx10 (ApplyExc ex) st k
      | (INL (all_tenv, args, dflts, ret, body, nr, mut), st) =>
          eval_exprs_cps cx10 es st (IntCallK all_tenv (ns, fn) args dflts ret body nr mut k)) ∧
  eval_exprs_cps cx11 [] st k = AK cx11 (ApplyVals []) st k ∧
  eval_exprs_cps cx12 (e::es) st k =
    eval_expr_cps cx12 e st (ExprsK es k)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (cx,e,st,k) => expr_size e
    | INR (cx,es,st,k) => list_size expr_size es)’
  \\ rw[expr1_size_map, SUM_MAP_expr2_size, list_size_SUM_MAP, MAP_MAP_o,
        list_size_pair_size_map, builtin_args_length_ok_def, check_def, type_check_def,
        assert_def, LENGTH_EQ_NUM_compute] \\ rw[]
End

val eval_expr_cps_pre_def = eval_expr_cps_def
   |> SRULE
        [liftk1, bind_def, ignore_bind_def,
         LET_RATOR, option_CASE_rator,
         sum_CASE_rator, prod_CASE_rator, lift_option_def]
   |> cv_auto_trans_pre "eval_expr_cps_pre eval_exprs_cps_pre";

Theorem eval_expr_cps_pre[cv_pre]:
  (∀a b c d. eval_expr_cps_pre a b c d) ∧
  (∀x y z w. eval_exprs_cps_pre x y z w)
Proof
  ho_match_mp_tac eval_expr_cps_ind \\ rw[]
  \\ rw[Once eval_expr_cps_pre_def]
  \\ gvs[CaseEq"prod", CaseEq"sum", CaseEq"option", raise_def, check_def, type_check_def,
         assert_def, builtin_args_length_ok_def, LENGTH_EQ_NUM_compute]
  \\ first_x_assum irule
  \\ gvs[bind_def, ignore_bind_def, lift_option_def, lift_option_type_def, assert_def]
QED

Definition eval_iterator_cps_def:
  eval_iterator_cps cx (Array e) st k =
    eval_expr_cps cx e st (ArrayK (expr_type e) k) ∧
  eval_iterator_cps cx (Range e1 e2) st k =
    eval_expr_cps cx e1 st (RangeK1 e2 k)
End

val () = cv_auto_trans eval_iterator_cps_def;

Definition eval_target_cps_def:
  eval_target_cps cx (BaseTarget t) st k =
    eval_base_target_cps cx t st (BaseTargetK k) ∧
  eval_target_cps cx (TupleTarget gs) st k =
    eval_targets_cps cx gs st (TupleTargetK k) ∧
  eval_targets_cps cx [] st k = AK cx (ApplyTargets []) st k ∧
  eval_targets_cps cx (g::gs) st k =
    eval_target_cps cx g st (TargetsK gs k)
End

val () = eval_target_cps_def |> cv_auto_trans;

Definition eval_stmt_cps_def:
  eval_stmt_cps cx Pass st k = AK cx Apply st k ∧
  eval_stmt_cps cx Continue st k = AK cx (ApplyExc ContinueException) st k ∧
  eval_stmt_cps cx Break st k = AK cx (ApplyExc BreakException) st k ∧
  eval_stmt_cps cx (Return NONE) st k = AK cx (ApplyExc (ReturnException NoneV)) st k ∧
  eval_stmt_cps cx (Return (SOME e)) st k = eval_expr_cps cx e st (ReturnK k) ∧
  eval_stmt_cps cx (Raise RaiseBare) st k =
    AK cx (ApplyExc (AssertException "")) st k ∧
  eval_stmt_cps cx (Raise RaiseUnreachable) st k =
    AK cx (ApplyExc (AssertException "UNREACHABLE")) st k ∧
  eval_stmt_cps cx (Raise (RaiseReason se)) st k =
    eval_expr_cps cx se st (RaiseK k) ∧
  eval_stmt_cps cx (Assert e reason) st k =
    eval_expr_cps cx e st (AssertK reason k) ∧
  eval_stmt_cps cx (Log id es) st k = eval_exprs_cps cx es st (LogK id k) ∧
  eval_stmt_cps cx (AnnAssign id typ e) st k =
    (case evaluate_type (get_tenv cx) typ of
       NONE => AK cx (ApplyExc (Error (TypeError "AnnAssign evaluate_type"))) st k
     | SOME tyv => eval_expr_cps cx e st (AnnAssignK id tyv k)) ∧
  eval_stmt_cps cx (Append t e) st k =
    eval_base_target_cps cx t st (AppendK e k) ∧
  eval_stmt_cps cx (Assign g e) st k =
    eval_target_cps cx g st (AssignK e k) ∧
  eval_stmt_cps cx (AugAssign ty t bop e) st k =
    eval_base_target_cps cx t st (AugAssignK ty bop e k) ∧
  eval_stmt_cps cx (If e ss1 ss2) st k =
    eval_expr_cps cx e st (IfK ss1 ss2 k) ∧
  eval_stmt_cps cx (For id typ it n body) st k =
    (case evaluate_type (get_tenv cx) typ of
       NONE => AK cx (ApplyExc (Error (TypeError "For evaluate_type"))) st k
     | SOME tyv => eval_iterator_cps cx it st (ForK id tyv n body k)) ∧
  eval_stmt_cps cx (Expr e) st k =
    eval_expr_cps cx e st (ExprK k)
End

val () = cv_auto_trans eval_stmt_cps_def;

Definition eval_stmts_cps_def:
  eval_stmts_cps cx [] st k = AK cx Apply st k ∧
  eval_stmts_cps cx (s::ss) st k =
    eval_stmt_cps cx s st (StmtsK ss k)
End

val () = cv_auto_trans eval_stmts_cps_def;

Definition eval_for_cps_def:
  eval_for_cps cx tyv nm body [] st k = AK cx Apply st k ∧
  eval_for_cps cx tyv nm body (v::vs) st k =
  (case push_scope_with_var nm tyv v st of
        (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_stmts_cps cx body st (ForK1 tyv nm body vs k))
End

val () = cv_auto_trans eval_for_cps_def;

Definition apply_def:
  apply cx st (StmtsK ss k) =
    eval_stmts_cps cx ss st k ∧
  apply cx st (ForK1 tyv nm body vs k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_for_cps cx tyv nm body vs st k) ∧
  apply cx st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx Apply st k) ∧
  apply cx st (IfK1 (Value (BoolV b)) ss1 ss2 k) =
    eval_stmts_cps cx (if b then ss1 else ss2) st (IfK2 k) ∧
  apply cx st (IfK1 (Value _) ss1 ss2 k) =
    AK cx (ApplyExc $ Error (TypeError "not BoolV")) st (IfK2 k) ∧
  apply cx st (IfK1 _ ss1 ss2 k) =
    AK cx (ApplyExc $ Error (TypeError "not Value")) st (IfK2 k) ∧
  apply cx st (IntCallK2 prev rtv nr is_view k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (do pop_function prev;
          (* Release reentrancy lock if nonreentrant and not view *)
          (if nr ∧ ¬is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ());
          crv <- lift_option_type (safe_cast rtv NoneV) "IntCall cast ret";
          return crv od st) k ∧
  apply cx st DoneK = AK cx Apply st DoneK ∧
  apply cx st _ = AK cx (ApplyExc $ Error (TypeError "apply k")) st DoneK
End

val () = apply_def
  |> SRULE [liftk1, ignore_bind_def, bind_def, prod_CASE_rator, sum_CASE_rator,
            COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

Definition apply_exc_def:
  apply_exc cx ex st (ReturnK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssertK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RaiseK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (LogK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AnnAssignK _ _ k) = AK cx (ApplyExc ex) st k ∧  (* id, tyv unused *)
  apply_exc cx ex st (AssignK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssignK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK1 _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK1 _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx (ApplyExc ex) st k) ∧
  apply_exc cx ex st (ForK _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ForK1 tyv nm body vs k) =
    (case finally (handle_loop_exception ex) pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL broke, st) =>
          if broke then AK cx Apply st k
          else eval_for_cps cx tyv nm body vs st k) ∧
  apply_exc cx ex st (ExprK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StmtsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ArrayK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RangeK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RangeK2 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BaseTargetK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TupleTargetK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TargetsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TargetsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeTargetK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptTargetK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptTargetK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfExpK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StructLitK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK1 _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (PopK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BuiltinK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (LenK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TypeBuiltinK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CallSendK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExtCallK _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawCallK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawLogK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawRevertK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SelfDestructK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CreateK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK _ _ _ _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK1 _ _ _ _ _ _ _ _ k) = AK (cx with stk updated_by TL) (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK2 prev rtv nr is_view k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (do rv <- finally (handle_function ex)
            (do pop_function prev;
                (* Release reentrancy lock if nonreentrant and not view *)
                if nr ∧ ¬is_view then
                  case cx.nonreentrant_slot of
                  | NONE => return ()
                  | SOME slot => release_nonreentrant_lock cx.txn.target slot
                else return ()
             od);
          crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
	  return crv od st)
      k ∧
  apply_exc cx ex st (ExprsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExprsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st DoneK = AK cx (ApplyExc ex) st DoneK
End

val () = apply_exc_def
  |> SRULE [finally_def, bind_def, ignore_bind_def,
            liftk1, prod_CASE_rator, sum_CASE_rator,
            COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

Definition apply_targets_def:
  apply_targets cx gvs st (TargetsK1 gv k) =
    AK cx (ApplyTargets (gv::gvs)) st k ∧
  apply_targets cx gvs st (TupleTargetK k) =
      AK cx (ApplyTarget (TupleTargetV gvs)) st k ∧
  apply_targets cx _ st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_targets k")) st DoneK
End

val () = cv_auto_trans apply_targets_def;

Definition apply_base_target_def:
  apply_base_target cx btv st (BaseTargetK k) =
    AK cx (ApplyTarget (BaseTargetV (FST btv) (SND btv))) st k ∧
  apply_base_target cx btv st (AttributeTargetK id k) =
    AK cx (ApplyBaseTarget (FST btv, AttrSubscript id :: SND btv)) st k ∧
  apply_base_target cx btv st (SubscriptTargetK e k) =
    eval_expr_cps cx e st (SubscriptTargetK1 btv k) ∧
  apply_base_target cx btv st (AugAssignK ty bop e k) =
    eval_expr_cps cx e st (AugAssignK1 ty btv bop k) ∧
  apply_base_target cx btv st (AppendK e k) =
    eval_expr_cps cx e st (AppendK1 btv k) ∧
  apply_base_target cx btv st (PopK k) =
    liftk cx ApplyTv (do
      sbs <<- SND btv;
      popped <- assign_target cx (BaseTargetV (FST btv) sbs) PopOp;
      v <- lift_option_type popped "Pop returned NONE";
      return $ Value v od st) k ∧
  apply_base_target cx btv st DoneK = AK cx (ApplyBaseTarget btv) st DoneK ∧
  apply_base_target cx _ st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_base_target k")) st DoneK
End

val () = apply_base_target_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            LET_RATOR, bind_def, ignore_bind_def]
  |> cv_auto_trans;

Definition apply_target_def:
  apply_target cx gv st (AssignK e k) =
    eval_expr_cps cx e st (AssignK1 gv k) ∧
  apply_target cx gv st (TargetsK gs k) =
    eval_targets_cps cx gs st (TargetsK1 gv k) ∧
  apply_target cx gv st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_target k")) st DoneK
End

val () = cv_auto_trans apply_target_def;

Definition apply_tv_def:
  apply_tv cx tv st (SubscriptK arr_typ e k) =
    eval_expr_cps cx e st (SubscriptK1 arr_typ tv k) ∧
  apply_tv cx tv st (IfK ss1 ss2 k) =
    liftk cx (K Apply) (push_scope st) (IfK1 tv ss1 ss2 k) ∧
  apply_tv cx tv st (LenK k) =
    liftk cx ApplyTv (do
      len <- toplevel_array_length cx tv;
      return $ Value $ IntV (&len)
    od st) k ∧
  apply_tv cx tv st (ExprK k) =
    (case type_check (¬is_HashMapRef tv) "Expr HashMapRef" st of
       (INR ex, st) => apply_exc cx ex st k
     | (INL (), st) => apply cx st k) ∧
  apply_tv cx tv st (ReturnK k) =
    liftk cx ApplyVal (materialise cx tv st) (ReturnK k) ∧
  apply_tv cx tv st (AnnAssignK id tyv k) =
    liftk cx ApplyVal (materialise cx tv st) (AnnAssignK id tyv k) ∧
  apply_tv cx tv st (AppendK1 btv k) =
    liftk cx ApplyVal (materialise cx tv st) (AppendK1 btv k) ∧
  apply_tv cx tv st (AssignK1 gv k) =
    liftk cx ApplyVal (materialise cx tv st) (AssignK1 gv k) ∧
  apply_tv cx tv st (ArrayK arr_typ k) =
    liftk cx ApplyVal (materialise cx tv st) (ArrayK arr_typ k) ∧
  apply_tv cx tv st (ExprsK es k) =
    liftk cx ApplyVal (materialise cx tv st) (ExprsK es k) ∧
  apply_tv cx tv st DoneK = AK cx (ApplyTv tv) st DoneK ∧
  apply_tv cx tv st k =
    liftk cx ApplyVal (get_Value tv st) k
End

val () = apply_tv_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_val_def:
  apply_val cx v st (ReturnK k) = apply_exc cx (ReturnException v) st k ∧
  apply_val cx (BoolV T) st (AssertK _ k) = apply cx st k ∧
  apply_val cx (BoolV F) st (AssertK AssertBare k) =
    apply_exc cx (AssertException "") st k ∧
  apply_val cx (BoolV F) st (AssertK AssertUnreachable k) =
    apply_exc cx (AssertException "UNREACHABLE") st k ∧
  apply_val cx (BoolV F) st (AssertK (AssertReason se) k) =
    eval_expr_cps cx se st (RaiseK k) ∧
  apply_val cx _ st (AssertK _ k) = apply_exc cx (Error (TypeError "not BoolV")) st k ∧
  apply_val cx (StringV str) st (RaiseK k) =
    apply_exc cx (AssertException str) st k ∧
  apply_val cx _ st (RaiseK k) =
    apply_exc cx (Error (TypeError "not StringV")) st k ∧
  apply_val cx v st (AnnAssignK id tyv k) =
    liftk cx (K Apply) (new_variable id tyv v st) k ∧
  apply_val cx v st (AssignK1 gv k) =
    liftk cx (K Apply) (assign_target cx gv (Replace v) st) k ∧
  apply_val cx v st (AugAssignK1 ty (loc, sbs) bop k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st) k ∧
  apply_val cx v st (AppendK1 (loc, sbs) k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (AppendOp v) st) k ∧
  apply_val cx v st (ArrayK arr_typ k) =
    (case evaluate_type (get_tenv cx) arr_typ of
     | SOME arr_tv =>
         liftk cx ApplyVals
           (lift_option_type (extract_elements arr_tv v) "For not ArrayV" st) k
     | NONE => AK cx (ApplyExc (Error (TypeError "For array type"))) st k) ∧
  apply_val cx v st (RangeK1 e k) = eval_expr_cps cx e st (RangeK2 v k) ∧
  apply_val cx v2 st (RangeK2 v1 k) =
    (case do rl <- lift_sum $ get_range_limits v1 v2;
             n1 <<- FST rl; n2 <<- SND rl;
             return $ GENLIST (λn. IntV (n1 + &n)) n2
     od st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL vs, st) => AK cx (ApplyVals vs) st k) ∧
  apply_val cx v st (SubscriptTargetK1 (loc, sbs) k) =
    (case lift_option_type (value_to_key v) "SubscriptTarget value_to_key" st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL sk, st) => apply_base_target cx (loc, sk :: sbs) st k) ∧
  apply_val cx (BoolV T) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e2 st k ∧
  apply_val cx (BoolV F) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e3 st k ∧
  apply_val cx v st (IfExpK _ _ k) =
    apply_exc cx (Error (TypeError "not BoolV")) st k ∧
  apply_val cx v2 st (SubscriptK1 arr_typ tv1 k) =
    liftk cx ApplyTv (do
      tenv <<- get_tenv cx;
      arr_tv <- lift_option_type (evaluate_type tenv arr_typ)
                  "Subscript array type";
      check_array_bounds cx tv1 v2;
      res <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
       case res of INL v => return v | INR (is_transient, slot, tv) => do
         v <- read_storage_slot cx is_transient slot tv;
         return $ Value v
       od
    od st) k ∧
  apply_val cx v st (AttributeK id k) =
    liftk cx (ApplyTv o Value) (lift_sum (evaluate_attribute v id) st) k ∧
  apply_val cx v st (ExprsK es k) =
    eval_exprs_cps cx es st (ExprsK1 v k) ∧
  apply_val cx v st DoneK = AK cx (ApplyVal v) st DoneK ∧
  apply_val cx v st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_val k")) st DoneK
End

val () = apply_val_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, lift_option_def, lift_option_type_def, lift_sum_def, lift_sum_runtime_def,
            LET_RATOR, bind_def, ignore_bind_def]
  |> cv_auto_trans;

Definition apply_vals_def:
  apply_vals cx vs st (ExprsK1 v k) =
    apply_vals cx (v::vs) st k ∧
  apply_vals cx vs st (ForK id tyv n body k) =
    (case do check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
             return vs od st
     of (INR ex, st) => apply_exc cx ex st k
      | (INL vs, st) => eval_for_cps cx tyv (string_to_num id) body vs st k) ∧
  apply_vals cx vs st (StructLitK ks k) =
    apply_tv cx (Value $ StructV (ZIP (ks, vs))) st k ∧
  apply_vals cx vs st (BuiltinK ty bt k) =
    liftk cx ApplyTv (do
      acc <- get_accounts;
      v <- lift_sum $ evaluate_builtin cx acc ty bt vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (TypeBuiltinK tb typ k) =
    liftk cx ApplyTv (do
      v <- lift_sum $ evaluate_type_builtin cx tb typ vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (LogK id k) =
    liftk cx (K Apply) (push_log (id, vs) st) k ∧
  apply_vals cx vs st (CallSendK k) =
    liftk cx ApplyTv (do
      type_check (LENGTH vs = 2) "CallSendK nargs";
      toAddr <- lift_option_type (dest_AddressV $ EL 0 vs) "Send not AddressV";
      amount <- lift_option_type (dest_NumV $ EL 1 vs) "Send not NumV";
      transfer_value cx.txn.target toAddr amount;
      return $ Value NoneV
    od st) k ∧
  apply_vals cx vs st (ExtCallK is_static func_name arg_types ret_type drv k) =
    (case do
      check (vs ≠ []) "ExtCall no target";
      target_addr <- lift_option_type (dest_AddressV (HD vs)) "ExtCall target not address";
      (* Convention: staticcall (T) args = [target; arg1; ...]
                     extcall (F) args = [target; value; arg1; ...] *)
      (value_opt, arg_vals) <- if is_static then
        return (NONE, TL vs)
      else do
        check (TL vs ≠ []) "ExtCall no value";
        v <- lift_option_type (dest_NumV (HD (TL vs))) "ExtCall value not int";
        return (SOME v, TL (TL vs))
      od;
      tenv <<- get_tenv cx;
      calldata <- lift_option (build_ext_calldata tenv func_name arg_types arg_vals)
                              "ExtCall build_calldata";
      accounts <- get_accounts;
      (* Vyper reverts if target has no code (EXTCODESIZE == 0) *)
      check (¬NULL (lookup_account target_addr accounts).code) "ExtCall target has no code";
      tStorage <- get_transient_storage;
      txParams <<- vyper_to_tx_params cx.txn;
      caller <<- cx.txn.target;
      result <- lift_option
        (run_ext_call caller target_addr calldata value_opt accounts tStorage txParams)
        "ExtCall run failed";
      (success, returnData, accounts', tStorage') <<- result;
      check success "ExtCall reverted";
      update_accounts (K accounts');
      update_transient (K tStorage');
      if returnData = [] ∧ IS_SOME drv then
        return (INL (THE drv))
      else do
        ret_val <- lift_sum_runtime (evaluate_abi_decode_return tenv ret_type returnData);
        return (INR (Value ret_val))
      od
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL (INL e), st) => eval_expr_cps cx e st k
     | (INL (INR tv), st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (IntCallK all_tenv src_fn args dflts ret body nr mut k) =
    eval_exprs_cps (cx with stk updated_by CONS src_fn)
      (DROP (LENGTH dflts - (LENGTH args - LENGTH vs)) dflts) st
      (IntCallK1 all_tenv src_fn args vs ret body nr mut k) ∧
  apply_vals cx dflt_vs st (IntCallK1 all_tenv src_fn args vs ret body nr mut k) =
    (case do
      env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs)) "IntCall bind_arguments";
      prev <- get_scopes;
      rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
      is_view <<- (mut = View ∨ mut = Pure);
      (* Acquire lock BEFORE push_function so scopes are unmodified on failure *)
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ());
      cxf <- push_function src_fn env (cx with stk updated_by TL);
      return (prev, cxf, body, rtv, is_view) od st
     of (INR ex, st) => apply_exc (cx with stk updated_by TL) ex st k
      | (INL (prev, cxf, body, rtv, is_view), st) =>
          eval_stmts_cps cxf body st (IntCallK2 prev rtv nr is_view k)) ∧
  (* ===== Chain interaction builtins ===== *)
  apply_vals cx vs st (RawCallK ty flags k) =
    (case do
      check (LENGTH vs = 3) "raw_call args";
      target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
      calldata <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
      amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
      value_opt <<- if flags.rcf_is_static then NONE else SOME amount;
      check (¬flags.rcf_is_delegate) "raw_call delegate unsupported";
      accounts <- get_accounts;
      tStorage <- get_transient_storage;
      txParams <<- vyper_to_tx_params cx.txn;
      caller <<- cx.txn.target;
      result <- lift_option
        (run_ext_call caller target_addr calldata value_opt accounts tStorage txParams)
        "raw_call run failed";
      (success, returnData, accounts', tStorage') <<- result;
      update_accounts (K accounts');
      update_transient (K tStorage');
      if flags.rcf_revert_on_failure then do
        check success "raw_call reverted";
        if flags.rcf_max_outsize = 0 then return $ Value NoneV
        else return $ Value $ BytesV (TAKE flags.rcf_max_outsize returnData)
      od else
        if flags.rcf_max_outsize = 0 then return $ Value $ BoolV success
        else return $ Value $ ArrayV $ TupleV [BoolV success;
               BytesV (TAKE flags.rcf_max_outsize returnData)]
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (RawLogK k) =
    (case do
      check (LENGTH vs = 2) "raw_log args";
      topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
      data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
      topic_vals <<- (case topics of
         TupleV tvs => tvs | DynArrayV tvs => tvs | _ => []);
      check (LENGTH topic_vals ≤ 4) "raw_log too many topics";
      push_log ((NONE,"raw_log"), topic_vals ++ [BytesV data]);
      return $ Value NoneV
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (RawRevertK k) =
    (case do
      check (LENGTH vs = 1) "raw_revert args";
      raise $ Error $ RuntimeError "raw_revert"
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (SelfDestructK k) =
    (case do
      check (LENGTH vs = 1) "selfdestruct args";
      target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
      accounts <- get_accounts;
      self_acct <<- lookup_account cx.txn.target accounts;
      balance <<- self_acct.balance;
      transfer_value cx.txn.target target_addr balance;
      return $ Value NoneV
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (CreateK ty kind rof k) =
    (case do
      check (vs ≠ []) "create no args";
      amount <- lift_option_type (dest_NumV (LAST vs)) "create value";
      target_addr <- lift_option_type (dest_AddressV (HD vs)) "create target";
      accounts <- get_accounts;
      self_acct <<- lookup_account cx.txn.target accounts;
      check (amount ≤ self_acct.balance) "create insufficient balance";
      new_addr <<- vfmContext$address_for_create cx.txn.target self_acct.nonce;
      existing <<- lookup_account new_addr accounts;
      check (¬vfmExecution$account_already_created existing) "address collision";
      if amount > 0 then
        transfer_value cx.txn.target new_addr amount
      else return ();
      update_accounts (vfmExecution$increment_nonce cx.txn.target);
      return $ Value $ AddressV new_addr
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st DoneK = AK cx (ApplyVals vs) st DoneK ∧
  apply_vals cx vs st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_vals k")) st DoneK
End

Triviality LET4_UNCURRY:
  (let (x,y,z,w) = M in N x y z w) =
     let p = M; x = FST p; p = SND p; y = FST p; p = SND p;
         z = FST p; w = SND p in N x y z w
Proof
  rw[UNCURRY]
QED

Triviality LET5_UNCURRY:
  (let (x,y,z,w,v) = M in N x y z w v) =
     let p = M; x = FST p; p = SND p; y = FST p; p = SND p;
         z = FST p; p = SND p; w = FST p; v = SND p in N x y z w v
Proof
  rw[UNCURRY]
QED

val apply_vals_pre_def = apply_vals_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, lift_option_def, lift_option_type_def, lift_option_type_def,
            lift_sum_def, lift_sum_runtime_def, prod_CASE_rator, LET_RATOR, LET4_UNCURRY, LET5_UNCURRY,
            UNCURRY, sum_CASE_rator, option_CASE_rator, COND_RATOR]
  |> cv_auto_trans_pre "apply_vals_pre";

Theorem apply_vals_pre[cv_pre]:
  ∀a b c d. apply_vals_pre a b c d
Proof
  ho_match_mp_tac apply_vals_ind \\ rw[]
  \\ rw[Once apply_vals_pre_def]
  \\ gvs[check_def, type_check_def, assert_def]
  \\ strip_tac \\ gvs[]
QED

Definition nextk_def[simp]:
  nextk (AK _ _ _ k) = k
End

val () = cv_auto_trans nextk_def;

Definition stepk_def:
  stepk (AK cx ak st k) =
  case ak of
     | Apply => apply cx st k
     | ApplyExc ex => apply_exc cx ex st k
     | ApplyTarget gv => apply_target cx gv st k
     | ApplyTargets gvs => apply_targets cx gvs st k
     | ApplyBaseTarget bv => apply_base_target cx bv st k
     | ApplyTv tv => apply_tv cx tv st k
     | ApplyVal v => apply_val cx v st k
     | ApplyVals vs => apply_vals cx vs st k
End

val () = cv_auto_trans stepk_def;

Definition cont_def:
  cont ak = OWHILE (λak. nextk ak ≠ DoneK) stepk ak
End

Triviality eval_expr_tail_cont_eq:
  ∀cx e st q r k.
  eval_expr cx e st = (q,r) ⇒
  cont (eval_expr_cps cx e st k) =
  cont ((case eval_expr cx e st of
           (INL tv,st1) => AK cx (ApplyTv tv) st1
         | (INR ex,st1) => AK cx (ApplyExc ex) st1) k) ⇒
  cont (eval_expr_cps cx e st k) =
  cont ((case q of
           INL tv => AK cx (ApplyTv tv) r
         | INR ex => AK cx (ApplyExc ex) r) k)
Proof
  rw[]
QED

Triviality extcall_nondefault_tail_cps_eq:
  ∀cx drv ret_type returnData ok_st err_st success q r1 q2 r2 k.
  ¬(returnData = [] ∧ IS_SOME drv) ∧
  ((case if success then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
      INL x =>
        (if returnData = [] ∧ IS_SOME drv then return (INL (THE drv))
         else do
           ret_val <-
             case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
               INL v => return v
             | INR str => raise (Error (RuntimeError str));
           return (INR (Value ret_val))
         od) ok_st
    | INR e => (INR e,err_st)) = (q,r1)) ∧
  ((case if success then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
      INL x =>
        (if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
         else do
           ret_val <-
             case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
               INL v => return v
             | INR str => raise (Error (RuntimeError str));
           return (Value ret_val)
         od) ok_st
    | INR e => (INR e,err_st)) = (q2,r2)) ⇒
  cont (case q of
          INL (INL e) => eval_expr_cps cx e r1 k
        | INL (INR tv) => AK cx (ApplyTv tv) r1 k
        | INR ex => AK cx (ApplyExc ex) r1 k) =
  cont ((case q2 of
           INL tv => AK cx (ApplyTv tv) r2
         | INR ex => AK cx (ApplyExc ex) r2) k)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on`success`
  >- (gvs[bind_def, return_def, raise_def, lift_sum_runtime_def] >>
      Cases_on`returnData = [] ∧ IS_SOME drv` >> gvs[] >>
      Cases_on`evaluate_abi_decode_return (get_tenv cx) ret_type returnData` >>
      gvs[bind_def, return_def, raise_def, lift_sum_runtime_def])
  \\ gvs[bind_def, return_def, raise_def, lift_sum_runtime_def]
QED

Triviality eval_expr_cps_owhile_result:
  ∀cx e st q r k.
  eval_expr cx e st = (q,r) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case eval_expr cx e st of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case q of
        INL tv => AK cx (ApplyTv tv) r
      | INR ex => AK cx (ApplyExc ex) r) k)
Proof
  rw[]
QED

Triviality extcall_success_empty_eta:
  ∀result ok1 ok2 err.
  (if FST result then INL ok1 else INR err) = INL ok2 ∧
  FST (SND result) = [] ⇒
  (T,[],FST (SND (SND result)),SND (SND (SND result))) = result
Proof
  rpt gen_tac >> PairCases_on`result` >> simp[]
QED

Triviality extcall_run_success_empty:
  ∀run_result call_res st ok1 ok2 err.
  run_result = (INL call_res,st) ∧
  (if FST call_res then INL ok1 else INR err) = INL ok2 ∧
  FST (SND call_res) = [] ⇒
  run_result =
    (INL (T,[],FST (SND (SND call_res)),SND (SND (SND call_res))),st)
Proof
  rpt gen_tac >> strip_tac >> PairCases_on`call_res` >> gvs[]
QED

Triviality extcall_default_tail_owhile_eq:
  ∀cx drv ret_type returnData st success q r1 q2 r2 k.
  returnData = [] ∧ IS_SOME drv ∧
  (∀st k.
     OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx (THE drv) st k) =
     OWHILE (λak. nextk ak ≠ DoneK) stepk
       ((case eval_expr cx (THE drv) st of
           (INL tv,st1) => AK cx (ApplyTv tv) st1
         | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) ∧
  ((case if success then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
      INL x =>
        (if returnData = [] ∧ IS_SOME drv then return (INL (THE drv))
         else do
           ret_val <-
             case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
               INL v => return v
             | INR str => raise (Error (RuntimeError str));
           return (INR (Value ret_val))
         od) st
    | INR e => (INR e,st)) = (q,r1)) ∧
  ((case if success then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
      INL x =>
        (if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
         else do
           ret_val <-
             case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
               INL v => return v
             | INR str => raise (Error (RuntimeError str));
           return (Value ret_val)
         od) st
    | INR e => (INR e,st)) = (q2,r2)) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (case q of
       INL (INL e) => eval_expr_cps cx e r1 k
     | INL (INR tv) => AK cx (ApplyTv tv) r1 k
     | INR ex => AK cx (ApplyExc ex) r1 k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case q2 of
        INL tv => AK cx (ApplyTv tv) r2
      | INR ex => AK cx (ApplyExc ex) r2) k)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on`success` >>
  gvs[return_def, raise_def, lift_sum_runtime_def] >>
  first_x_assum (qspecl_then[`r1`,`k`] mp_tac) >>
  qpat_x_assum `eval_expr cx (THE drv) r1 = (q2,r2)` mp_tac >>
  simp[]
QED

Triviality extcall_default_bigstep_eval_eq:
  ∀cx drv ret_type returnData st success ok q r.
  returnData = [] ∧ IS_SOME drv ∧
  ((if success then INL () else INR (Error (RuntimeError "ExtCall reverted"))) = INL ok) ∧
  ((case if success then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
      INL x =>
        (if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
         else do
           ret_val <-
             case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
               INL v => return v
             | INR str => raise (Error (RuntimeError str));
           return (Value ret_val)
         od) st
    | INR e => (INR e,st)) = (q,r)) ⇒
  eval_expr cx (THE drv) st = (q,r)
Proof
  rpt gen_tac >> strip_tac >> Cases_on`success` >> gvs[]
QED

Triviality extcall_no_value_default_owhile_eq:
  ∀cx x e r target_addr s_addr calldata s_call call_st accounts' tStorage' q st' k func_name arg_types.
  x ≠ [] ∧
  (case dest_AddressV (HD x) of
     NONE => raise (Error (TypeError "ExtCall target not address"))
   | SOME v => return v) r = (INL target_addr,s_addr) ∧
  (case build_ext_calldata (get_tenv cx) func_name arg_types (TL x) of
     NONE => raise (Error (RuntimeError "ExtCall build_calldata"))
   | SOME v => return v) s_addr = (INL calldata,s_call) ∧
  ¬NULL (lookup_account target_addr s_call.accounts).code ∧
  (case
     run_ext_call cx.txn.target target_addr calldata NONE s_call.accounts s_call.tStorage
       (vyper_to_tx_params cx.txn)
   of
     NONE => raise (Error (RuntimeError "ExtCall run failed"))
   | SOME v => return v) s_call = (INL (T,[],accounts',tStorage'),call_st) ∧
  eval_expr cx e (call_st with <|accounts := accounts'; tStorage := tStorage'|>) = (q,st') ∧
  (∀s_check t_check s_addr0 target_addr0 t_addr s_build calldata0 t_build
     s_get_acc accounts t_get_acc s_check_code t_check_code s_get_ts tStorage t_get_ts
     s_run t_run success accounts0 tStorage0 s_check_success t_check_success
     s_update_acc t_update_acc s_update_ts t_update_ts st0 k0.
     check T "ExtCall no target" s_check = (INL (),t_check) ∧
     lift_option_type (dest_AddressV (HD x)) "ExtCall target not address" s_addr0 =
       (INL target_addr0,t_addr) ∧
     lift_option (build_ext_calldata (get_tenv cx) func_name arg_types (TL x))
       "ExtCall build_calldata" s_build = (INL calldata0,t_build) ∧
     get_accounts s_get_acc = (INL accounts,t_get_acc) ∧
     check (¬NULL (lookup_account target_addr0 accounts).code) "ExtCall target has no code"
       s_check_code = (INL (),t_check_code) ∧
     get_transient_storage s_get_ts = (INL tStorage,t_get_ts) ∧
     lift_option
       (run_ext_call cx.txn.target target_addr0 calldata0 NONE accounts tStorage
          (vyper_to_tx_params cx.txn)) "ExtCall run failed" s_run =
       (INL (success,[],accounts0,tStorage0),t_run) ∧
     check success "ExtCall reverted" s_check_success = (INL (),t_check_success) ∧
     update_accounts (K accounts0) s_update_acc = (INL (),t_update_acc) ∧
     update_transient (K tStorage0) s_update_ts = (INL (),t_update_ts) ⇒
     OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st0 k0) =
     OWHILE (λak. nextk ak ≠ DoneK) stepk
       ((case eval_expr cx e st0 of
           (INL tv,st1) => AK cx (ApplyTv tv) st1
         | (INR ex,st1) => AK cx (ApplyExc ex) st1) k0)) ⇒
  cont (eval_expr_cps cx e (call_st with <|accounts := accounts'; tStorage := tStorage'|>) k) =
  cont ((case q of INL tv => AK cx (ApplyTv tv) st' | INR ex => AK cx (ApplyExc ex) st') k)
Proof
  rpt gen_tac >> strip_tac >> simp[cont_def] >>
  qpat_x_assum `∀s_check t_check s_addr0 target_addr0 t_addr s_build calldata0 t_build
                    s_get_acc accounts t_get_acc s_check_code t_check_code s_get_ts
                    tStorage t_get_ts s_run t_run success accounts0 tStorage0
                    s_check_success t_check_success s_update_acc t_update_acc
                    s_update_ts t_update_ts st0 k0. _`
    (qspecl_then[
      `r`,`r`,`r`,`target_addr`,`s_addr`,`s_addr`,`calldata`,`s_call`,
      `s_call`,`s_call.accounts`,`s_call`,`s_call`,`s_call`,
      `s_call`,`s_call.tStorage`,`s_call`,`s_call`,`call_st`,
      `T`,`accounts'`,`tStorage'`,`call_st`,`call_st`,
      `call_st`,`call_st with accounts := accounts'`,
      `call_st with accounts := accounts'`,
      `call_st with <|accounts := accounts'; tStorage := tStorage'|>`,
      `call_st with <|accounts := accounts'; tStorage := tStorage'|>`,
      `k`] mp_tac) >>
  simp[check_def, lift_option_def, lift_option_type_def,
       get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def,
       return_def, raise_def] >>
  strip_tac >>
  irule eval_expr_cps_owhile_result >> simp[] >>
  qpat_x_assum `_ ⇒ OWHILE _ stepk (eval_expr_cps cx e _ k) = _` mp_tac >>
  simp[assert_def]
QED

Triviality apply_exc_owhile_eq:
  ∀cx ex st k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk (AK cx (ApplyExc ex) st k) =
  (if k ≠ DoneK then OWHILE (λak. nextk ak ≠ DoneK) stepk (apply_exc cx ex st k)
   else SOME (AK cx (ApplyExc ex) st DoneK))
Proof
  rw[Once OWHILE_THM, stepk_def]
QED

Triviality apply_exc_owhile_unfold_eq:
  ∀cx ex st k.
  (if nextk (apply_exc cx ex st k) ≠ DoneK then
     OWHILE (λak. nextk ak ≠ DoneK) stepk (stepk (apply_exc cx ex st k))
   else SOME (apply_exc cx ex st k)) =
  (if k ≠ DoneK then
     OWHILE (λak. nextk ak ≠ DoneK) stepk (apply_exc cx ex st k)
   else SOME (AK cx (ApplyExc ex) st DoneK))
Proof
  rpt gen_tac >> Cases_on`k = DoneK` >> gvs[]
  >- rw[apply_exc_def, stepk_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [OWHILE_THM])) >>
  rw[]
QED

Triviality context_stk_pop_push[simp]:
  ∀cx src_fn. (cx with stk updated_by TL ∘ CONS src_fn) = cx
Proof
  rw[evaluation_context_component_equality, o_DEF, FUN_EQ_THM]
QED

Triviality intcall_nonview_prefix_error_eq:
  ∀cx src_fn args vs dflt_vs ret body r' ex st.
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot F) s3
                  of
                    (INL (),s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) => (INL (prev,cxf,body,rtv,F),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INR ex,st) ⇒
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot F) s3
                  of
                    (INL (),s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) =>
                           (case
                              finally
                                (try
                                   do x <- eval_stmts cxf body; return NoneV od
                                   handle_function)
                                do
                                  x <- pop_function prev;
                                  (case cx.nonreentrant_slot of
                                     NONE => return ()
                                   | SOME slot =>
                                       release_nonreentrant_lock cx.txn.target slot)
                                od s5
                            of
                              (INL rv,s6) =>
                                (case lift_option_type (safe_cast rtv rv)
                                        "IntCall cast ret" s6 of
                                   (INL crv,s7) => (INL (Value crv),s7)
                                 | (INR e,s7) => (INR e,s7))
                            | (INR e,s6) => (INR e,s6))
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INR ex,st)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INR ex,st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def,
           finally_def, try_def])
QED

Triviality intcall_prefix_error_eq:
  ∀cx src_fn args vs dflt_vs ret body r' is_view ex st.
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view) s3
                  of
                    (INL (),s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) => (INL (prev,cxf,body,rtv,is_view),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INR ex,st) ⇒
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view) s3
                  of
                    (INL (),s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) =>
                           (case
                              finally
                                (try
                                   do x <- eval_stmts cxf body; return NoneV od
                                   handle_function)
                                do
                                  x <- pop_function prev;
                                  if ¬is_view then
                                    (case cx.nonreentrant_slot of
                                       NONE => return ()
                                     | SOME slot =>
                                         release_nonreentrant_lock cx.txn.target slot)
                                  else return ()
                                od s5
                            of
                              (INL rv,s6) =>
                                (case lift_option_type (safe_cast rtv rv)
                                        "IntCall cast ret" s6 of
                                   (INL crv,s7) => (INL (Value crv),s7)
                                 | (INR e,s7) => (INR e,s7))
                            | (INR e,s6) => (INR e,s6))
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INR ex,st)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INR ex,st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def,
           finally_def, try_def])
QED

Triviality intcall_prefix_error_nolock_eq:
  ∀cx src_fn args vs dflt_vs ret body r' is_view ex st.
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case push_function src_fn env cx s3 of
                    (INL cxf,s4) => (INL (prev,cxf,body,rtv,is_view),s4)
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INR ex,st) ⇒
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case push_function src_fn env cx s3 of
                    (INL cxf,s4) =>
                      (case
                         finally
                           (try do x <- eval_stmts cxf body; return NoneV od
                            handle_function)
                           (do x <- pop_function prev; return () od) s4
                       of
                         (INL rv,s5) =>
                           (case lift_option_type (safe_cast rtv rv)
                                   "IntCall cast ret" s5 of
                              (INL crv,s6) => (INL (Value crv),s6)
                            | (INR e,s6) => (INR e,s6))
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INR ex,st)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INR ex,st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def,
           finally_def, try_def])
QED

Triviality intcall_prefix_success_missing_slot:
  ∀cx src_fn args vs dflt_vs ret body r' is_view call_res st.
  cx.nonreentrant_slot = NONE ⇒
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view) s3
                  of
                    (INL (),s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) => (INL (prev,cxf,body,rtv,is_view),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,st) ⇒
  F
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,st)` mp_tac >>
  gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_prefix_success_missing_slot_eq:
  ∀cx src_fn args vs dflt_vs ret body r' is_view call_res st.
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case NONE of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view) s3
                  of
                    (INL (),s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) => (INL (prev,cxf,body,rtv,is_view),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,st) ⇒
  F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_prefix_success_missing_slot_raise_eq:
  ∀cx src_fn args vs dflt_vs ret body r' is_view call_res st.
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case raise (Error (RuntimeError "nonreentrant slot missing")) s3 of
                    (INL (),s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) => (INL (prev,cxf,body,rtv,is_view),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,st) ⇒
  F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_nonview_prefix_success_facts:
  ∀cx src_fn args vs dflt_vs ret body r' call_res st.
  (case lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
          "IntCall bind_arguments" r' of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type (evaluate_type (get_tenv cx) ret)
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot F) s3
                  of
                    (INL lock_ok,s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) => (INL (prev,cxf,body,rtv,F),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,st) ⇒
  ∃env s1 prev s2 rtv s3 s4 cxf.
    lift_option_type (bind_arguments (get_tenv cx) args (vs ⧺ dflt_vs))
      "IntCall bind_arguments" r' = (INL env,s1) ∧
    get_scopes s1 = (INL prev,s2) ∧
    lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret" s2 =
      (INL rtv,s3) ∧
    (case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot F) s3 =
      (INL (),s4) ∧
    push_function src_fn env cx s4 = (INL cxf,st) ∧
    call_res = (prev,cxf,body,rtv,F)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_nonview_prefix_success_tup_facts:
  ∀cx src_fn tup vs dflt_vs st call_res prefix_st.
  (case lift_option_type
          (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
          "IntCall bind_arguments" st of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type
                    (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot F) s3
                  of
                    (INL lock_ok,s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) =>
                           (INL (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,F),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,prefix_st) ⇒
  ∃env s1 prev s2 rtv s3 s4 cxf.
    lift_option_type
      (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
      "IntCall bind_arguments" st = (INL env,s1) ∧
    get_scopes s1 = (INL prev,s2) ∧
    lift_option_type
      (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
      "IntCall eval ret" s2 = (INL rtv,s3) ∧
    (case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot F) s3 =
      (INL (),s4) ∧
    push_function src_fn env cx s4 = (INL cxf,prefix_st) ∧
    call_res = (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,F)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,prefix_st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_prefix_success_tup_facts:
  ∀cx src_fn tup vs dflt_vs st call_res prefix_st.
  (case lift_option_type
          (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
          "IntCall bind_arguments" st of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type
                    (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot =>
                         acquire_nonreentrant_lock cx.txn.target slot
                           (FST tup = View ∨ FST tup = Pure)) s3
                  of
                    (INL lock_ok,s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) =>
                           (INL
                              (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,
                               FST tup = View ∨ FST tup = Pure),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,prefix_st) ⇒
  ∃env s1 prev s2 rtv s3 s4 cxf.
    lift_option_type
      (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
      "IntCall bind_arguments" st = (INL env,s1) ∧
    get_scopes s1 = (INL prev,s2) ∧
    lift_option_type
      (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
      "IntCall eval ret" s2 = (INL rtv,s3) ∧
    (case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot =>
         acquire_nonreentrant_lock cx.txn.target slot
           (FST tup = View ∨ FST tup = Pure)) s3 = (INL (),s4) ∧
    push_function src_fn env cx s4 = (INL cxf,prefix_st) ∧
    call_res =
      (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,
       FST tup = View ∨ FST tup = Pure)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,prefix_st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_prefix_success_nolock_tup_facts:
  ∀cx src_fn tup vs dflt_vs st is_view call_res prefix_st.
  (case lift_option_type
          (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
          "IntCall bind_arguments" st of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type
                    (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case push_function src_fn env cx s3 of
                    (INL cxf,s4) =>
                      (INL
                         (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,is_view),s4)
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,prefix_st) ⇒
  ∃env s1 prev s2 rtv s3 cxf.
    lift_option_type
      (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
      "IntCall bind_arguments" st = (INL env,s1) ∧
    get_scopes s1 = (INL prev,s2) ∧
    lift_option_type
      (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
      "IntCall eval ret" s2 = (INL rtv,s3) ∧
    push_function src_fn env cx s3 = (INL cxf,prefix_st) ∧
    call_res =
      (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,is_view)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,prefix_st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_prefix_success_tup_facts_by_view:
  ∀cx src_fn tup vs dflt_vs st is_view call_res prefix_st.
  (case lift_option_type
          (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
          "IntCall bind_arguments" st of
     (INL env,s1) =>
       (case get_scopes s1 of
          (INL prev,s2) =>
            (case lift_option_type
                    (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
                    "IntCall eval ret" s2 of
               (INL rtv,s3) =>
                 (case
                    (case cx.nonreentrant_slot of
                       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
                     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view) s3
                  of
                    (INL lock_ok,s4) =>
                      (case push_function src_fn env cx s4 of
                         (INL cxf,s5) =>
                           (INL
                              (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,is_view),s5)
                       | (INR e,s5) => (INR e,s5))
                  | (INR e,s4) => (INR e,s4))
             | (INR e,s3) => (INR e,s3))
        | (INR e,s2) => (INR e,s2))
   | (INR e,s1) => (INR e,s1)) = (INL call_res,prefix_st) ⇒
  ∃env s1 prev s2 rtv s3 s4 cxf.
    lift_option_type
      (bind_arguments (get_tenv cx) (FST (SND (SND tup))) (vs ⧺ dflt_vs))
      "IntCall bind_arguments" st = (INL env,s1) ∧
    get_scopes s1 = (INL prev,s2) ∧
    lift_option_type
      (evaluate_type (get_tenv cx) (FST (SND (SND (SND (SND tup))))))
      "IntCall eval ret" s2 = (INL rtv,s3) ∧
    (case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view) s3 =
      (INL (),s4) ∧
    push_function src_fn env cx s4 = (INL cxf,prefix_st) ∧
    call_res =
      (prev,cxf,SND (SND (SND (SND (SND tup)))),rtv,is_view)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = (INL call_res,prefix_st)` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, return_def, raise_def])
QED

Triviality intcall_k2_apply_success_eq:
  ∀cx src_fn prev rtv r' k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (apply (cx with stk updated_by CONS src_fn) r' (IntCallK2 prev rtv T F k)) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case
        case
          do
            do
              x <- pop_function prev;
              case cx.nonreentrant_slot of
                NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            od;
            return NoneV
          od r'
        of
          (INL rv,s'') =>
            (case lift_option_type (safe_cast rtv rv) "IntCall cast ret" s'' of
               (INL crv,s'') => (INL (Value crv),s'')
             | (INR e,s'') => (INR e,s''))
        | (INR e,s'') => (INR e,s'')
      of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)
Proof
  rw[apply_def, liftk1, ignore_bind_def, bind_def,
     pop_function_def, return_def, set_scopes_def, context_stk_pop_push] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  gvs[] >>
  Cases_on
    `(case cx.nonreentrant_slot of
        NONE => return ()
      | SOME slot => release_nonreentrant_lock cx.txn.target slot)
       (r' with scopes := prev)` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
  qmatch_asmsub_rename_tac
    `lift_option_type (safe_cast rtv NoneV) "IntCall cast ret" cast_st` >>
  Cases_on `lift_option_type (safe_cast rtv NoneV) "IntCall cast ret" cast_st` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def]
QED

Triviality intcall_k2_apply_success_view_eq:
  ∀cx src_fn prev rtv r' k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (apply (cx with stk updated_by CONS src_fn) r' (IntCallK2 prev rtv T T k)) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case
        case lift_option_type (safe_cast rtv NoneV) "IntCall cast ret"
               (r' with scopes := prev) of
          (INL crv,s'') => (INL (Value crv),s'')
        | (INR e,s'') => (INR e,s'')
      of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)
Proof
  rw[apply_def, liftk1, ignore_bind_def, bind_def,
     pop_function_def, return_def, set_scopes_def, context_stk_pop_push] >>
  Cases_on `lift_option_type (safe_cast rtv NoneV) "IntCall cast ret"
              (r' with scopes := prev)` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def]
QED

Triviality intcall_k2_apply_success_nolock_eq:
  ∀cx src_fn prev rtv is_view r' k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (apply (cx with stk updated_by CONS src_fn) r'
       (IntCallK2 prev rtv F is_view k)) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case
        case lift_option_type (safe_cast rtv NoneV) "IntCall cast ret"
               (r' with scopes := prev) of
          (INL crv,s'') => (INL (Value crv),s'')
        | (INR e,s'') => (INR e,s'')
      of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)
Proof
  rw[apply_def, liftk1, ignore_bind_def, bind_def,
     pop_function_def, return_def, set_scopes_def, context_stk_pop_push] >>
  Cases_on `lift_option_type (safe_cast rtv NoneV) "IntCall cast ret"
              (r' with scopes := prev)` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def]
QED

Triviality intcall_k2_apply_exc_nolock_eq:
  ∀cx src_fn prev rtv is_view ex st k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (apply_exc (cx with stk updated_by CONS src_fn) ex st
       (IntCallK2 prev rtv F is_view k)) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case
        case
          finally (handle_function ex)
            (do x <- pop_function prev; return () od) st
        of
          (INL rv,s'') =>
            (case lift_option_type (safe_cast rtv rv) "IntCall cast ret" s'' of
               (INL crv,s'') => (INL (Value crv),s'')
             | (INR e,s'') => (INR e,s''))
        | (INR e,s'') => (INR e,s'')
      of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)
Proof
  rw[apply_exc_def, o_DEF, liftk1, bind_def, ignore_bind_def,
     finally_def, return_def, pop_function_def, set_scopes_def,
     raise_def, context_stk_pop_push] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac
    `case final_res of
       (INL rv,s'') =>
         (case lift_option_type (safe_cast rtv rv) "IntCall cast ret" s'' of
            (INL crv,s'') => (INL crv,s'')
          | (INR e,s'') => (INR e,s''))
     | (INR e,s'') => (INR e,s'')` >>
  PairCases_on `final_res` >> Cases_on `final_res0` >>
  gvs[bind_def, return_def, raise_def] >>
  qmatch_asmsub_rename_tac
    `lift_option_type (safe_cast rtv cast_val) "IntCall cast ret" cast_st` >>
  Cases_on `lift_option_type (safe_cast rtv cast_val) "IntCall cast ret" cast_st` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def]
QED

Triviality intcall_k2_apply_exc_eq:
  ∀cx src_fn prev rtv ex st k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (apply_exc (cx with stk updated_by CONS src_fn) ex st
       (IntCallK2 prev rtv T F k)) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case
        case
          finally (handle_function ex)
            (do
               x <- pop_function prev;
               case cx.nonreentrant_slot of
                 NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             od) st
        of
          (INL rv,s'') =>
            (case lift_option_type (safe_cast rtv rv) "IntCall cast ret" s'' of
               (INL crv,s'') => (INL (Value crv),s'')
             | (INR e,s'') => (INR e,s''))
        | (INR e,s'') => (INR e,s'')
      of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)
Proof
  rw[apply_exc_def, o_DEF, liftk1, bind_def, ignore_bind_def,
     finally_def, return_def, pop_function_def, set_scopes_def,
     raise_def, context_stk_pop_push] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac
    `case final_res of
       (INL rv,s'') =>
         (case lift_option_type (safe_cast rtv rv) "IntCall cast ret" s'' of
            (INL crv,s'') => (INL crv,s'')
          | (INR e,s'') => (INR e,s''))
     | (INR e,s'') => (INR e,s'')` >>
  PairCases_on `final_res` >> Cases_on `final_res0` >>
  gvs[bind_def, return_def, raise_def] >>
  qmatch_asmsub_rename_tac
    `lift_option_type (safe_cast rtv cast_val) "IntCall cast ret" cast_st` >>
  Cases_on `lift_option_type (safe_cast rtv cast_val) "IntCall cast ret" cast_st` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def]
QED

Triviality intcall_k2_apply_exc_view_eq:
  ∀cx src_fn prev rtv ex st k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (apply_exc (cx with stk updated_by CONS src_fn) ex st
       (IntCallK2 prev rtv T T k)) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case
        case
          finally (handle_function ex)
            (do x <- pop_function prev; return () od) st
        of
          (INL rv,s'') =>
            (case lift_option_type (safe_cast rtv rv) "IntCall cast ret" s'' of
               (INL crv,s'') => (INL (Value crv),s'')
             | (INR e,s'') => (INR e,s''))
        | (INR e,s'') => (INR e,s'')
      of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)
Proof
  rw[apply_exc_def, o_DEF, liftk1, bind_def, ignore_bind_def,
     finally_def, return_def, pop_function_def, set_scopes_def,
     raise_def, context_stk_pop_push] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac
    `case final_res of
       (INL rv,s'') =>
         (case lift_option_type (safe_cast rtv rv) "IntCall cast ret" s'' of
            (INL crv,s'') => (INL crv,s'')
          | (INR e,s'') => (INR e,s''))
     | (INR e,s'') => (INR e,s'')` >>
  PairCases_on `final_res` >> Cases_on `final_res0` >>
  gvs[bind_def, return_def, raise_def] >>
  qmatch_asmsub_rename_tac
    `lift_option_type (safe_cast rtv cast_val) "IntCall cast ret" cast_st` >>
  Cases_on `lift_option_type (safe_cast rtv cast_val) "IntCall cast ret" cast_st` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def]
QED

Triviality extcall_value_full_default_owhile_eq:
  ∀cx x e r target_addr s_addr value_num value_state calldata build_st run_st
     accounts tStorage accounts' tStorage' call_st q st' k func_name arg_types.
  x ≠ [] ∧ TL x ≠ [] ∧
  (case dest_AddressV (HD x) of
     NONE => raise (Error (TypeError "ExtCall target not address"))
   | SOME v => return v) r = (INL target_addr,s_addr) ∧
  (case dest_NumV (HD (TL x)) of
     NONE => raise (Error (TypeError "ExtCall value not int"))
   | SOME v => return v) s_addr = (INL value_num,value_state) ∧
  (case build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL x)) of
     NONE => raise (Error (RuntimeError "ExtCall build_calldata"))
   | SOME v => return v) value_state = (INL calldata,build_st) ∧
  ¬NULL (lookup_account target_addr accounts).code ∧
  (case
     run_ext_call cx.txn.target target_addr calldata (SOME value_num) accounts
       tStorage (vyper_to_tx_params cx.txn)
   of
     NONE => raise (Error (RuntimeError "ExtCall run failed"))
   | SOME v => return v) run_st = (INL (T,[],accounts',tStorage'),call_st) ∧
  eval_expr cx e (call_st with <|accounts := accounts'; tStorage := tStorage'|>) = (q,st') ∧
  (∀s_check t_check s_addr0 target_addr0 t_addr s_value value_opt arg_vals t_value
     s_build calldata0 t_build s_get_acc accounts t_get_acc s_check_code t_check_code
     s_get_ts tStorage t_get_ts s_run t_run success accounts0 tStorage0
     s_check_success t_check_success s_update_acc t_update_acc s_update_ts t_update_ts st0 k0.
     check T "ExtCall no target" s_check = (INL (),t_check) ∧
     lift_option_type (dest_AddressV (HD x)) "ExtCall target not address" s_addr0 =
       (INL target_addr0,t_addr) ∧
     do
       check T "ExtCall no value";
       v <- lift_option_type (dest_NumV (HD (TL x))) "ExtCall value not int";
       return (SOME v,TL (TL x))
     od s_value = (INL (value_opt,arg_vals),t_value) ∧
     lift_option (build_ext_calldata (get_tenv cx) func_name arg_types arg_vals)
       "ExtCall build_calldata" s_build = (INL calldata0,t_build) ∧
     get_accounts s_get_acc = (INL accounts,t_get_acc) ∧
     check (¬NULL (lookup_account target_addr0 accounts).code) "ExtCall target has no code"
       s_check_code = (INL (),t_check_code) ∧
     get_transient_storage s_get_ts = (INL tStorage,t_get_ts) ∧
     lift_option
       (run_ext_call cx.txn.target target_addr0 calldata0 value_opt accounts tStorage
          (vyper_to_tx_params cx.txn)) "ExtCall run failed" s_run =
       (INL (success,[],accounts0,tStorage0),t_run) ∧
     check success "ExtCall reverted" s_check_success = (INL (),t_check_success) ∧
     update_accounts (K accounts0) s_update_acc = (INL (),t_update_acc) ∧
     update_transient (K tStorage0) s_update_ts = (INL (),t_update_ts) ⇒
     OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st0 k0) =
     OWHILE (λak. nextk ak ≠ DoneK) stepk
       ((case eval_expr cx e st0 of
           (INL tv,st1) => AK cx (ApplyTv tv) st1
         | (INR ex,st1) => AK cx (ApplyExc ex) st1) k0)) ⇒
  cont (eval_expr_cps cx e (call_st with <|accounts := accounts'; tStorage := tStorage'|>) k) =
  cont ((case q of INL tv => AK cx (ApplyTv tv) st' | INR ex => AK cx (ApplyExc ex) st') k)
Proof
  rpt gen_tac >> strip_tac >> simp[cont_def] >>
  qpat_x_assum `∀s_check t_check s_addr0 target_addr0 t_addr s_value value_opt arg_vals t_value
                    s_build calldata0 t_build s_get_acc accounts t_get_acc s_check_code t_check_code
                    s_get_ts tStorage t_get_ts s_run t_run success accounts0 tStorage0
                    s_check_success t_check_success s_update_acc t_update_acc
                    s_update_ts t_update_ts st0 k0. _`
    (qspecl_then[
      `r`,`r`,`r`,`target_addr`,`s_addr`,`s_addr`,`SOME value_num`,`TL (TL x)`,`value_state`,
      `value_state`,`calldata`,`build_st`,`run_st with accounts := accounts`,`accounts`,`run_st with accounts := accounts`,
      `run_st with accounts := accounts`,`run_st with accounts := accounts`,`run_st with tStorage := tStorage`,`tStorage`,`run_st with tStorage := tStorage`,`run_st`,`call_st`,
      `T`,`accounts'`,`tStorage'`,`call_st`,`call_st`,
      `call_st`,`call_st with accounts := accounts'`,
      `call_st with accounts := accounts'`,
      `call_st with <|accounts := accounts'; tStorage := tStorage'|>`,
      `call_st with <|accounts := accounts'; tStorage := tStorage'|>`,
      `k`] mp_tac) >>
  simp[check_def, lift_option_def, lift_option_type_def,
       get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def,
       bind_def, ignore_bind_def, assert_def, return_def, raise_def] >>
  strip_tac >>
  irule eval_expr_cps_owhile_result >> simp[] >>
  qpat_x_assum `_ ⇒ OWHILE _ stepk (eval_expr_cps cx e _ k) = _` mp_tac >>
  simp[]
QED

Triviality extcall_value_full_default_context_eq:
  ∀cx x e r target_addr s_addr value_num value_state calldata build_st
     accounts accounts_st tStorage run_st accounts' tStorage' call_st q st' k
     func_name arg_types.
  x ≠ [] ∧ TL x ≠ [] ∧
  (case dest_AddressV (HD x) of
     NONE => raise (Error (TypeError "ExtCall target not address"))
   | SOME v => return v) r = (INL target_addr,s_addr) ∧
  (case dest_NumV (HD (TL x)) of
     NONE => raise (Error (TypeError "ExtCall value not int"))
   | SOME v => return v) s_addr = (INL value_num,value_state) ∧
  (case build_ext_calldata (get_tenv cx) func_name arg_types (SND (SOME value_num,TL (TL x))) of
     NONE => raise (Error (RuntimeError "ExtCall build_calldata"))
   | SOME v => return v) value_state = (INL calldata,build_st) ∧
  return build_st.accounts build_st = (INL accounts,accounts_st) ∧
  return accounts_st.tStorage accounts_st = (INL tStorage,run_st) ∧
  ¬NULL (lookup_account target_addr accounts).code ∧
  (case
     run_ext_call cx.txn.target target_addr calldata (FST (SOME value_num,TL (TL x)))
       accounts tStorage (vyper_to_tx_params cx.txn)
   of
     NONE => raise (Error (RuntimeError "ExtCall run failed"))
   | SOME v => return v) run_st = (INL (T,[],accounts',tStorage'),call_st) ∧
  eval_expr cx e (call_st with <|accounts := accounts'; tStorage := tStorage'|>) = (q,st') ∧
  (∀s_check t_check s_addr0 target_addr0 t_addr s_value value_opt arg_vals t_value
     s_build calldata0 t_build s_get_acc accounts t_get_acc s_check_code t_check_code
     s_get_ts tStorage t_get_ts s_run t_run success accounts0 tStorage0
     s_check_success t_check_success s_update_acc t_update_acc s_update_ts t_update_ts st0 k0.
     check T "ExtCall no target" s_check = (INL (),t_check) ∧
     lift_option_type (dest_AddressV (HD x)) "ExtCall target not address" s_addr0 =
       (INL target_addr0,t_addr) ∧
     do
       check T "ExtCall no value";
       v <- lift_option_type (dest_NumV (HD (TL x))) "ExtCall value not int";
       return (SOME v,TL (TL x))
     od s_value = (INL (value_opt,arg_vals),t_value) ∧
     lift_option (build_ext_calldata (get_tenv cx) func_name arg_types arg_vals)
       "ExtCall build_calldata" s_build = (INL calldata0,t_build) ∧
     get_accounts s_get_acc = (INL accounts,t_get_acc) ∧
     check (¬NULL (lookup_account target_addr0 accounts).code) "ExtCall target has no code"
       s_check_code = (INL (),t_check_code) ∧
     get_transient_storage s_get_ts = (INL tStorage,t_get_ts) ∧
     lift_option
       (run_ext_call cx.txn.target target_addr0 calldata0 value_opt accounts tStorage
          (vyper_to_tx_params cx.txn)) "ExtCall run failed" s_run =
       (INL (success,[],accounts0,tStorage0),t_run) ∧
     check success "ExtCall reverted" s_check_success = (INL (),t_check_success) ∧
     update_accounts (K accounts0) s_update_acc = (INL (),t_update_acc) ∧
     update_transient (K tStorage0) s_update_ts = (INL (),t_update_ts) ⇒
     OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st0 k0) =
     OWHILE (λak. nextk ak ≠ DoneK) stepk
       ((case eval_expr cx e st0 of
           (INL tv,st1) => AK cx (ApplyTv tv) st1
         | (INR ex,st1) => AK cx (ApplyExc ex) st1) k0)) ⇒
  cont (eval_expr_cps cx e (call_st with <|accounts := accounts'; tStorage := tStorage'|>) k) =
  cont ((case q of INL tv => AK cx (ApplyTv tv) st' | INR ex => AK cx (ApplyExc ex) st') k)
Proof
  rpt gen_tac >> strip_tac >> gvs[return_def] >>
  drule_all extcall_value_full_default_owhile_eq >> simp[]
QED

Triviality extcall_value_arg_premise:
  ∀x s v st arg_vals.
  TL x ≠ [] ∧
  (case dest_NumV (HD (TL x)) of
     NONE => raise (Error (TypeError "ExtCall value not int"))
   | SOME v => return v) s = (INL v,st) ∧
  TL (TL x) = arg_vals ⇒
  do
    assert T (Error (RuntimeError "ExtCall no value"));
    v <-
      case dest_NumV (HD (TL x)) of
        NONE => raise (Error (TypeError "ExtCall value not int"))
      | SOME v => return v;
    return (SOME v,arg_vals)
  od s = (INL (SOME v,arg_vals),st)
Proof
  rw[bind_def, ignore_bind_def, assert_def, return_def, raise_def]
QED

Triviality extcall_value_arg_premise_refl:
  ∀x s v st.
  TL x ≠ [] ∧
  (case dest_NumV (HD (TL x)) of
     NONE => raise (Error (TypeError "ExtCall value not int"))
   | SOME v => return v) s = (INL v,st) ⇒
  do
    assert T (Error (RuntimeError "ExtCall no value"));
    v <-
      case dest_NumV (HD (TL x)) of
        NONE => raise (Error (TypeError "ExtCall value not int"))
      | SOME v => return v;
    return (SOME v,TL (TL x))
  od s = (INL (FST (SOME v,TL (TL x)),SND (SOME v,TL (TL x))),st)
Proof
  rw[bind_def, ignore_bind_def, assert_def, return_def, raise_def]
QED

Triviality extcall_value_default_owhile_eq:
  ∀cx e x s v st q r final_st k.
  TL x ≠ [] ∧
  (case dest_NumV (HD (TL x)) of
     NONE => raise (Error (TypeError "ExtCall value not int"))
   | SOME v => return v) s = (INL v,st) ∧
  (∀t s0.
     do
       assert T (Error (RuntimeError "ExtCall no value"));
       v <-
         case dest_NumV (HD (TL x)) of
           NONE => raise (Error (TypeError "ExtCall value not int"))
         | SOME v => return v;
       return (SOME v,TL (TL x))
     od s0 = (INL (FST (SOME v,TL (TL x)),SND (SOME v,TL (TL x))),t) ⇒
     ∀st' k.
       OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st' k) =
       OWHILE (λak. nextk ak ≠ DoneK) stepk
         ((case eval_expr cx e st' of
             (INL tv,st1) => AK cx (ApplyTv tv) st1
           | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) ∧
  eval_expr cx e final_st = (q,r) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e final_st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case q of
        INL tv => AK cx (ApplyTv tv) r
      | INR ex => AK cx (ApplyExc ex) r) k)
Proof
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then[`st`,`s`] mp_tac) >>
  impl_tac >- rw[bind_def, ignore_bind_def, assert_def, return_def, raise_def] >>
  strip_tac >>
  first_x_assum (qspecl_then[`final_st`,`k`] mp_tac) >>
  simp[]
QED

Triviality extcall_value_default_owhile_from_arg_eq:
  ∀cx e x v arg_st arg_res q r final_st k.
  (do
     assert T (Error (RuntimeError "ExtCall no value"));
     v <-
       case dest_NumV (HD (TL x)) of
         NONE => raise (Error (TypeError "ExtCall value not int"))
       | SOME v => return v;
     return (SOME v,TL (TL x))
   od arg_st = (INL (SOME v,TL (TL x)),arg_res)) ∧
  (∀t s0.
     do
       assert T (Error (RuntimeError "ExtCall no value"));
       v <-
         case dest_NumV (HD (TL x)) of
           NONE => raise (Error (TypeError "ExtCall value not int"))
         | SOME v => return v;
       return (SOME v,TL (TL x))
     od s0 = (INL (FST (SOME v,TL (TL x)),SND (SOME v,TL (TL x))),t) ⇒
     ∀st' k.
       OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st' k) =
       OWHILE (λak. nextk ak ≠ DoneK) stepk
         ((case eval_expr cx e st' of
             (INL tv,st1) => AK cx (ApplyTv tv) st1
           | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) ∧
  eval_expr cx e final_st = (q,r) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e final_st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case q of
        INL tv => AK cx (ApplyTv tv) r
      | INR ex => AK cx (ApplyExc ex) r) k)
Proof
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then[`arg_res`,`arg_st`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  first_x_assum (qspecl_then[`final_st`,`k`] mp_tac) >>
  simp[]
QED

Triviality extcall_result_owhile_eq:
  ∀cx drv ret_type result_res cps_q cps_st big_q big_st k.
  (∀st k.
     OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx (THE drv) st k) =
     OWHILE (λak. nextk ak ≠ DoneK) stepk
       ((case eval_expr cx (THE drv) st of
           (INL tv,st1) => AK cx (ApplyTv tv) st1
         | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) ∧
  ((case result_res of
      (INL result,st) =>
        (case if FST result then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
           INL x =>
             (if FST (SND result) = [] ∧ IS_SOME drv then return (INL (THE drv))
              else do
                ret_val <-
                  case evaluate_abi_decode_return (get_tenv cx) ret_type (FST (SND result)) of
                    INL v => return v
                  | INR str => raise (Error (RuntimeError str));
                return (INR (Value ret_val))
              od)
               (st with <|accounts := FST (SND (SND result));
                         tStorage := SND (SND (SND result))|>)
         | INR e => (INR e,st))
    | (INR e,st) => (INR e,st)) = (cps_q,cps_st)) ∧
  ((case result_res of
      (INL result,st) =>
        (case if FST result then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
           INL x =>
             (if FST (SND result) = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
              else do
                ret_val <-
                  case evaluate_abi_decode_return (get_tenv cx) ret_type (FST (SND result)) of
                    INL v => return v
                  | INR str => raise (Error (RuntimeError str));
                return (Value ret_val)
              od)
               (st with <|accounts := FST (SND (SND result));
                         tStorage := SND (SND (SND result))|>)
         | INR e => (INR e,st))
    | (INR e,st) => (INR e,st)) = (big_q,big_st)) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (case cps_q of
       INL (INL e) => eval_expr_cps cx e cps_st k
     | INL (INR tv) => AK cx (ApplyTv tv) cps_st k
     | INR ex => AK cx (ApplyExc ex) cps_st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case big_q of
        INL tv => AK cx (ApplyTv tv) big_st
      | INR ex => AK cx (ApplyExc ex) big_st) k)
Proof
  rpt gen_tac >> strip_tac >>
  PairCases_on`result_res` >> Cases_on`result_res0` >> gvs[] >-
   (PairCases_on`x` >> Cases_on`x0` >>
    gvs[return_def, raise_def, lift_sum_runtime_def] >>
    reverse (Cases_on`x1 = [] ∧ IS_SOME drv`) >>
    gvs[return_def, raise_def, lift_sum_runtime_def] >-
     (Cases_on`evaluate_abi_decode_return (get_tenv cx) ret_type x1` >>
      gvs[bind_def, return_def, raise_def, lift_sum_runtime_def]) >>
    first_x_assum (qspecl_then[
      `result_res1 with <|accounts := x2; tStorage := x3|>`,`k`] mp_tac) >>
    qpat_x_assum `eval_expr cx (THE drv) _ = (big_q,big_st)` mp_tac >>
    simp[])
QED

Triviality extcall_decoded_monad_owhile_eq:
  ∀cx (dec_m : evaluation_state -> (value + exception) # evaluation_state) st cps_q cps_st big_q big_st k.
  (do
     ret_val <- dec_m;
     return (INR (Value ret_val))
   od st = (cps_q,cps_st)) ∧
  (do
     ret_val <- dec_m;
     return (Value ret_val)
   od st = (big_q,big_st)) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (case cps_q of
       INL (INL e) => eval_expr_cps cx e cps_st k
     | INL (INR tv) => AK cx (ApplyTv tv) cps_st k
     | INR ex => AK cx (ApplyExc ex) cps_st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case big_q of
        INL tv => AK cx (ApplyTv tv) big_st
      | INR ex => AK cx (ApplyExc ex) big_st) k)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on`dec_m st` >> Cases_on`q` >>
  gvs[bind_def, return_def]
QED

Triviality extcall_decoded_pair_owhile_eq:
  ∀cx decoded_res cps_q cps_st big_q big_st k.
  ((case decoded_res of
      (INL ret_val,st) => (INL (INR (Value ret_val)),st)
    | (INR e,st) => (INR e,st)) = (cps_q,cps_st)) ∧
  ((case decoded_res of
      (INL ret_val,st) => (INL (Value ret_val),st)
    | (INR e,st) => (INR e,st)) = (big_q,big_st)) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (case cps_q of
       INL (INL e) => eval_expr_cps cx e cps_st k
     | INL (INR tv) => AK cx (ApplyTv tv) cps_st k
     | INR ex => AK cx (ApplyExc ex) cps_st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case big_q of
        INL tv => AK cx (ApplyTv tv) big_st
      | INR ex => AK cx (ApplyExc ex) big_st) k)
Proof
  rpt gen_tac >> strip_tac >> PairCases_on`decoded_res` >> Cases_on`decoded_res0` >> gvs[]
QED

Triviality extcall_decoded_pair_cont_eq:
  ∀cx decoded_res cps_q cps_st big_q big_st k.
  ((case decoded_res of
      (INL ret_val,st) => (INL (Value ret_val),st)
    | (INR e,st) => (INR e,st)) = (big_q,big_st)) ⇒
  ((case decoded_res of
      (INL ret_val,st) => (INL (INR (Value ret_val)),st)
    | (INR e,st) => (INR e,st)) = (cps_q,cps_st)) ⇒
  cont (case cps_q of
          INL (INL e) => eval_expr_cps cx e cps_st k
        | INL (INR tv) => AK cx (ApplyTv tv) cps_st k
        | INR ex => AK cx (ApplyExc ex) cps_st k) =
  cont ((case big_q of
           INL tv => AK cx (ApplyTv tv) big_st
         | INR ex => AK cx (ApplyExc ex) big_st) k)
Proof
  rw[cont_def] >>
  irule extcall_decoded_pair_owhile_eq >>
  qexists_tac`decoded_res` >>
  simp[]
QED

Triviality extcall_decoded_tail_owhile_eq:
  ∀cx decoded st cps_q cps_st big_q big_st k.
  ((case decoded of
      INL ret_val => (INL (INR (Value ret_val)),st)
    | INR e => (INR e,st)) = (cps_q,cps_st)) ∧
  ((case decoded of
      INL ret_val => (INL (Value ret_val),st)
    | INR e => (INR e,st)) = (big_q,big_st)) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    (case cps_q of
       INL (INL e) => eval_expr_cps cx e cps_st k
     | INL (INR tv) => AK cx (ApplyTv tv) cps_st k
     | INR ex => AK cx (ApplyExc ex) cps_st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case big_q of
        INL tv => AK cx (ApplyTv tv) big_st
      | INR ex => AK cx (ApplyExc ex) big_st) k)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on`decoded` >> gvs[]
QED

Triviality extcall_decoded_tail_cont_eq:
  ∀cx decoded st cps_q cps_st big_q big_st k.
  ((case decoded of
      INL ret_val => (INL (Value ret_val),st)
    | INR e => (INR e,st)) = (big_q,big_st)) ⇒
  ((case decoded of
      INL ret_val => (INL (INR (Value ret_val)),st)
    | INR e => (INR e,st)) = (cps_q,cps_st)) ⇒
  cont (case cps_q of
          INL (INL e) => eval_expr_cps cx e cps_st k
        | INL (INR tv) => AK cx (ApplyTv tv) cps_st k
        | INR ex => AK cx (ApplyExc ex) cps_st k) =
  cont ((case big_q of
           INL tv => AK cx (ApplyTv tv) big_st
         | INR ex => AK cx (ApplyExc ex) big_st) k)
Proof
  rw[cont_def] >> Cases_on`decoded` >> gvs[]
QED

Triviality extcall_default_tail_cps_eq:
  ∀cx drv ret_type returnData st success q r1 q2 r2 k.
  returnData = [] ∧ IS_SOME drv ∧
  (success ⇒ ∀st k.
     cont (eval_expr_cps cx (THE drv) st k) =
     cont ((case eval_expr cx (THE drv) st of
              (INL tv,st1) => AK cx (ApplyTv tv) st1
            | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) ∧
  ((case if success then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
      INL x =>
        (if returnData = [] ∧ IS_SOME drv then return (INL (THE drv))
         else do
           ret_val <-
             case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
               INL v => return v
             | INR str => raise (Error (RuntimeError str));
           return (INR (Value ret_val))
         od) st
    | INR e => (INR e,st)) = (q,r1)) ∧
  ((case if success then INL () else INR (Error (RuntimeError "ExtCall reverted")) of
      INL x =>
        (if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
         else do
           ret_val <-
             case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
               INL v => return v
             | INR str => raise (Error (RuntimeError str));
           return (Value ret_val)
         od) st
    | INR e => (INR e,st)) = (q2,r2)) ⇒
  cont (case q of
          INL (INL e) => eval_expr_cps cx e r1 k
        | INL (INR tv) => AK cx (ApplyTv tv) r1 k
        | INR ex => AK cx (ApplyExc ex) r1 k) =
  cont ((case q2 of
           INL tv => AK cx (ApplyTv tv) r2
         | INR ex => AK cx (ApplyExc ex) r2) k)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on`success` >>
  gvs[return_def, raise_def, lift_sum_runtime_def] >>
  qpat_x_assum `∀st k. _` (qspecl_then[`r1`,`k`]mp_tac) >>
  qpat_x_assum `eval_expr cx (THE drv) r1 = (q2,r2)` mp_tac >>
  simp[]
QED

Theorem eval_cps_eq:
 (∀cx s st k.
     cont (eval_stmt_cps cx s st k) =
     cont ((
       case eval_stmt cx s st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx ss st k.
     cont (eval_stmts_cps cx ss st k) =
     cont ((
       case eval_stmts cx ss st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx it st k.
     cont (eval_iterator_cps cx it st k) =
     cont ((
       case eval_iterator cx it st
         of (INL vs, st1) => (AK cx (ApplyVals vs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx g st k.
     cont (eval_target_cps cx g st k) =
     cont ((
       case eval_target cx g st
         of (INL gv, st1) => (AK cx (ApplyTarget gv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx gs st k.
     cont (eval_targets_cps cx gs st k) =
     cont ((
       case eval_targets cx gs st
         of (INL gvs, st1) => (AK cx (ApplyTargets gvs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx bt st k.
     cont (eval_base_target_cps cx bt st k) =
     cont ((
       case eval_base_target cx bt st
         of (INL bv, st1) => (AK cx (ApplyBaseTarget bv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx tyv nm body vs st k.
     cont (eval_for_cps cx tyv nm body vs st k) =
     cont ((
       case eval_for cx tyv nm body vs st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx e st k.
     cont (eval_expr_cps cx e st k) =
     cont ((
       case eval_expr cx e st
         of (INL tv, st1) => (AK cx (ApplyTv tv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx es st k.
     cont (eval_exprs_cps cx es st k) =
     cont ((
       case eval_exprs cx es st
         of (INL vs, st1) => (AK cx (ApplyVals vs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k))
(* CPS-big-step equivalence *)
Proof
  ho_match_mp_tac evaluate_ind
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, return_def] (* Pass *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Continue *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Break *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Return NONE *)
  \\ conj_tac >- ( (* Return (SOME e) *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[cont_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[cont_def]
    \\ rw[Once OWHILE_THM, stepk_def]
    \\ rw[apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[raise_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, stepk_def, SimpRHS] \\ gvs[]
    \\ rw[apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Raise RaiseBare *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Raise RaiseUnreachable *)
  \\ conj_tac >- ( (* Raise (RaiseReason se) *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ reverse (Cases_on `x`) \\ simp[get_Value_def, raise_def, return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[Once OWHILE_THM, stepk_def]
    \\ Cases_on`v`
    \\ simp[dest_StringV_def, lift_option_def, lift_option_type_def, return_def,
            raise_def, apply_val_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM] )
  \\ conj_tac >- ( (* Assert e AssertBare *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ qmatch_goalsub_rename_tac`get_Value tv`
    \\ reverse $ Cases_on`tv` \\ rw[return_def, raise_def, get_Value_def]
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ simp[switch_BoolV_def] \\ rw[return_def, raise_def]
    >- ( (* BoolV T *)
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_def] )
    >- ( (* BoolV F *)
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
    \\ Cases_on`v` \\ gvs[] (* else: not BoolV *)
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Assert e AssertUnreachable *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ qmatch_goalsub_rename_tac`get_Value tv`
    \\ reverse $ Cases_on`tv` \\ rw[return_def, raise_def, get_Value_def]
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ simp[switch_BoolV_def] \\ rw[return_def, raise_def]
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_def] )
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
    \\ Cases_on`v` \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Assert e (AssertReason se) *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ qmatch_goalsub_rename_tac`get_Value tv`
    \\ reverse $ Cases_on`tv` \\ rw[return_def, raise_def, get_Value_def]
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ simp[switch_BoolV_def] \\ rw[return_def, raise_def]
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_def] )
    >- ( (* BoolV F: eval reason expr *)
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ first_x_assum drule \\ rw[cont_def]
      \\ rw[bind_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
      \\ qmatch_goalsub_rename_tac`get_Value stv`
      \\ reverse $ Cases_on`stv` \\ rw[get_Value_def, return_def, raise_def]
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def]
      \\ rename1`Value sv`
      \\ Cases_on`sv`
      \\ simp[dest_StringV_def, lift_option_def, lift_option_type_def,
              return_def, raise_def, apply_val_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
    \\ Cases_on`v` \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Log id es *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def, liftk1])
  \\ conj_tac >- ( (* AnnAssign id typ e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    \\ gvs[lift_option_type_def, raise_def, return_def, cont_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ reverse CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, liftk1, apply_val_def] )
  \\ conj_tac >- ( (* Append t e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def, UNCURRY, ignore_bind_def]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ qmatch_goalsub_rename_tac`AppendK1 btv`
    \\ Cases_on`btv`
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- ( (* Assign g e — target→expr→materialise→assign *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_target_def]
    \\ gvs[cont_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1,
          ignore_bind_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def])
  \\ conj_tac >- ( (* AugAssign t bop e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ qmatch_goalsub_rename_tac`AugAssignK1 _ p` \\ Cases_on`p`
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ gvs[oneline get_Value_def, toplevel_value_CASE_rator,
           CaseEq"toplevel_value", CaseEq"prod", raise_def, return_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1, bind_def,
          ignore_bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def])
  \\ conj_tac >- ( (* If e ss1 ss2 *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def, ignore_bind_def, UNCURRY]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_def]
    \\ first_x_assum drule \\ rw[]
    \\ first_x_assum drule \\ rw[]
    \\ gvs[switch_BoolV_def]
    \\ IF_CASES_TAC \\ gvs[]
    >- (
      rw[apply_def, finally_def, bind_def, ignore_bind_def]
      \\ gvs[push_scope_def, return_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- (
        rw[Once OWHILE_THM, stepk_def, apply_exc_def]
        \\ CASE_TAC \\ CASE_TAC \\ rw[raise_def] )
      \\ rw[Once OWHILE_THM, stepk_def, apply_def]
      \\ CASE_TAC \\ CASE_TAC )
    \\ IF_CASES_TAC \\ gvs[]
    >- (
      rw[apply_def, finally_def, bind_def, ignore_bind_def]
      \\ gvs[push_scope_def, return_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- (
        rw[Once OWHILE_THM, stepk_def, apply_exc_def]
        \\ CASE_TAC \\ CASE_TAC \\ rw[raise_def] )
      \\ rw[Once OWHILE_THM, stepk_def, apply_def]
      \\ CASE_TAC \\ CASE_TAC )
    \\ qmatch_goalsub_abbrev_tac`TypeError str`
    \\ gvs[push_scope_def, return_def]
    \\ reverse $ Cases_on`x`
    \\ rw[apply_def, finally_def, raise_def, ignore_bind_def, bind_def]
    \\ gvs[]
    >- (
      rw[pop_scope_def, return_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[pop_scope_def, return_def] )
    \\ Cases_on `v` \\ rw[apply_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[pop_scope_def, return_def] )
  \\ conj_tac >- ( (* For id typ it n body *)
    rw[eval_stmt_cps_def, evaluate_def, ignore_bind_def, bind_def,
       lift_option_type_def, return_def, raise_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[return_def, raise_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ gvs[return_def]
    \\ first_x_assum $ drule_then drule
    \\ rw[] )
  \\ conj_tac >- ( (* Expr e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ rw[ignore_bind_def, bind_def, return_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_val_def]
    \\ gvs[] \\ rw[apply_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- rw[eval_stmts_cps_def, evaluate_def, return_def] (* eval_stmts [] *)
  \\ conj_tac >- ( (* eval_stmts (s::ss) *)
    rw[eval_stmts_cps_def, evaluate_def, return_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_def]
    \\ gvs[]
    \\ first_x_assum drule \\ rw[])
  \\ conj_tac >- ( (* eval_iterator (Array e) *)
    rw[eval_iterator_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1,
          lift_option_type_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def, raise_def]
    \\ gvs[raise_def] )
  \\ conj_tac >- ( (* eval_iterator (Range e1 e2) *)
    rw[eval_iterator_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ gvs[]
    \\ first_x_assum $ drule_then drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ rw[bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] ))
  \\ conj_tac >- ( (* eval_target (BaseTarget t) *)
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- ( (* eval_target (TupleTarget gs) *)
    rw[eval_target_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_targets_def, return_def] )
  \\ conj_tac >- rw[eval_target_cps_def, evaluate_def, bind_def, return_def] (* eval_targets [] *)
  \\ conj_tac >- ( (* eval_targets (g::gs) *)
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_target_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_targets_def] )
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, liftk1] (* eval_base_target (NameTarget id) *)
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, liftk1] (* eval_base_target (BareGlobalNameTarget id) *)
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, return_def] (* eval_base_target (TopLevelNameTarget ...) *)
  \\ conj_tac >- ( (* eval_base_target (AttributeTarget t id) *)
    rw[eval_base_target_cps_def, evaluate_def, bind_def, UNCURRY, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- ( (* eval_base_target (SubscriptTarget t e) *)
    rw[eval_base_target_cps_def, evaluate_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ qmatch_asmsub_rename_tac`INL p` \\ PairCases_on`p`
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ qmatch_asmsub_rename_tac`get_Value tv`
    \\ Cases_on`tv` \\ gvs[get_Value_def, raise_def, return_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      gvs[lift_option_def, lift_option_type_def, option_CASE_rator, CaseEq"option",
          raise_def, return_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
    \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- rw[eval_for_cps_def, evaluate_def, return_def] (* eval_for [] *)
  \\ conj_tac >- ( (* eval_for (v::vs) *)
    rw[eval_for_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC \\ gvs[]
    \\ first_assum drule \\ simp_tac std_ss [] \\ disch_then kall_tac
    \\ rw[finally_def, try_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, finally_def]
      \\ CASE_TAC \\ CASE_TAC
      \\ rw[ignore_bind_def, bind_def, return_def, raise_def]
      \\ CASE_TAC \\ CASE_TAC
      \\ rw[return_def]
      \\ last_x_assum drule \\ rw[]
      \\ last_x_assum drule \\ rw[]
      \\ gvs[finally_def, bind_def, try_def, CaseEq"prod", CaseEq"sum",
             PULL_EXISTS, ignore_bind_def, return_def, raise_def]
      \\ fsrw_tac[DNF_ss][]
      \\ last_x_assum drule \\ rw[])
    \\ rw[return_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def]
    \\ last_x_assum drule \\ rw[]
    \\ gvs[finally_def, bind_def, try_def, CaseEq"prod", CaseEq"sum",
           PULL_EXISTS, ignore_bind_def, return_def, raise_def]
    \\ fsrw_tac[DNF_ss][]
    \\ last_x_assum drule \\ rw[]
    \\ last_x_assum drule \\ rw[])
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1] (* eval_expr (Name id) *)
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1] (* eval_expr (BareGlobalName id) *)
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1] (* eval_expr (TopLevelName ...) *)
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1] (* eval_expr (FlagMember ...) *)
  \\ conj_tac >- ( (* eval_expr (IfExp e1 e2 e3) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ first_x_assum drule
    \\ first_x_assum drule
    \\ rw[]
    \\ simp[switch_BoolV_def]
    >> simp[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ IF_CASES_TAC \\ gvs[return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ IF_CASES_TAC \\ gvs[return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ simp[raise_def]
    \\ Cases_on`x` \\ gvs[return_def]
    >- (
      Cases_on`v`
      \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def] )
    \\ gvs[raise_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def] (* eval_expr (Literal l) *)
  \\ conj_tac >- ( (* eval_expr (StructLit ...) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def]
    \\ gvs[]
    \\ simp[apply_tv_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* eval_expr (Subscript e1 e2) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def]
    \\ CASE_TAC \\ reverse CASE_TAC)
  \\ conj_tac >- ( (* eval_expr (Attribute e id) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- ( (* eval_expr (Builtin bt es) *)
    simp[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ rpt strip_tac
    \\ BasicProvers.TOP_CASE_TAC
    \\ gvs[cont_def]
    \\ BasicProvers.TOP_CASE_TAC
    \\ gvs[] \\ first_x_assum drule
    \\ first_x_assum drule
    \\ rw[bind_def]
    \\ (CASE_TAC \\ reverse CASE_TAC
        >- rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def,
          apply_tv_def, bind_def, liftk1]
    >> CASE_TAC \\ CASE_TAC \\ rw[return_def] )
  \\ conj_tac >- ( (* eval_expr (Pop bt) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def, bind_def, liftk1] )
  \\ conj_tac >- ( (* eval_expr (TypeBuiltin ...) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1] )
  \\ conj_tac >- ( (* eval_expr (Call Send es _) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def,
          bind_def, ignore_bind_def, liftk1]
    \\ qmatch_goalsub_abbrev_tac`type_check b c d`
    \\ `type_check b c d = (INL (), d)`
    by (
      rw[check_def, type_check_def, assert_def, Abbr`b`]
      \\ drule eval_exprs_length
      \\ gvs[check_def, type_check_def, assert_def] )
    \\ rw[] )
  \\ conj_tac >- ( (* ExtCall *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[Once OWHILE_THM, stepk_def, apply_vals_def, liftk1]
    \\ qmatch_goalsub_abbrev_tac`pair_CASE cc1`
    \\ qmatch_goalsub_abbrev_tac`lhs = _`
    \\ qmatch_goalsub_abbrev_tac`pair_CASE cc2`
    \\ qunabbrev_tac`lhs`
    \\ Cases_on`cc1` \\ Cases_on`cc2` \\ gvs[]
    \\ Cases_on`is_static'`
    \\ simp[return_def]
    \\ simp[bind_def, ignore_bind_def,CaseEq"prod",CaseEq"sum"]
    \\ TRY pairarg_tac \\ simp[bind_def,CaseEq"prod",CaseEq"sum"]
    \\ TRY pairarg_tac \\ simp[bind_def,CaseEq"prod",CaseEq"sum"]
    \\ gvs[return_def, lift_sum_runtime_def, raise_def, AllCaseEqs()]
    \\ TRY (Cases_on`x'` \\ fs[pairTheory.FST, pairTheory.SND])
    \\ first_x_assum drule
    \\ strip_tac
    \\ qpat_x_assum `_ = (q,r')` mp_tac
    \\ simp[bind_def, ignore_bind_def, return_def, raise_def,
            lift_sum_runtime_def, check_def, assert_def,
            lift_option_def, lift_option_type_def,
            get_accounts_def, get_transient_storage_def,
            update_accounts_def, update_transient_def, AllCaseEqs()]
    \\ strip_tac
    \\ qpat_x_assum `_ = (q',r'')` mp_tac
    \\ simp[bind_def, ignore_bind_def, return_def, raise_def,
            lift_sum_runtime_def, check_def, assert_def,
            lift_option_def, lift_option_type_def,
            get_accounts_def, get_transient_storage_def,
            update_accounts_def, update_transient_def, AllCaseEqs()]
    \\ strip_tac
    \\ TRY (qpat_x_assum `_ = (q,r')` mp_tac)
    \\ TRY (qpat_x_assum `_ = (q',r'')` mp_tac)
    \\ PURE_REWRITE_TAC[pairTheory.ELIM_UNCURRY]
    \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def,
            assert_def, update_accounts_def, update_transient_def]
    \\ TRY strip_tac
    \\ TRY strip_tac
    \\ reverse (Cases_on`FST (SND result) = [] /\ IS_SOME drv`)
    >- (simp[GSYM cont_def]
        \\ qmatch_asmsub_abbrev_tac`base_st with <|accounts := FST (SND (SND result)); tStorage := SND (SND (SND result))|>`
        \\ irule extcall_nondefault_tail_cps_eq
        \\ qexists_tac`drv`
        \\ qexists_tac`base_st`
        \\ qexists_tac`base_st with <|accounts := FST (SND (SND result)); tStorage := SND (SND (SND result))|>`
        \\ qexists_tac`ret_type`
        \\ qexists_tac`FST (SND result)`
        \\ qexists_tac`FST result`
        \\ Cases_on`FST (SND result) = []`
        \\ Cases_on`drv`
        \\ gvs[Abbr`base_st`])
    \\ simp[GSYM cont_def]
    \\ PairCases_on`result`
    \\ fs[pairTheory.FST, pairTheory.SND]
    \\ Cases_on`drv` \\ fs[]
    \\ TRY (Cases_on`result0`)
    \\ TRY (drule_all extcall_default_bigstep_eval_eq \\ strip_tac)
    \\ TRY (qpat_x_assum `_ = (q,r')` mp_tac
            \\ simp[return_def, raise_def]
            \\ strip_tac)
    \\ TRY (qpat_x_assum `_ = (q',r'')` mp_tac
            \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
            \\ strip_tac)
    \\ TRY (drule_all extcall_default_bigstep_eval_eq \\ strip_tac)
    \\ TRY (qpat_x_assum `eval_expr cx _ _ = (q',r'')` (fn th => assume_tac th))
    \\ TRY (qpat_x_assum `INL (INL _) = q` (SUBST_ALL_TAC o SYM)
            \\ qpat_x_assum `_ = r'` (SUBST_ALL_TAC o SYM)
            \\ drule_all extcall_no_value_default_owhile_eq
            \\ simp[])
    \\ TRY (qmatch_asmsub_rename_tac`(case dest_NumV (HD (TL x)) of
              NONE => raise (Error (TypeError "ExtCall value not int"))
            | SOME v => return v) value_st = (INL value_num,value_state)`
            \\ qpat_x_assum `INL (INL _) = q` (SUBST_ALL_TAC o SYM)
            \\ qpat_x_assum `_ = r'` (SUBST_ALL_TAC o SYM)
            \\ simp[cont_def]
            \\ irule extcall_value_default_owhile_eq
            \\ qexists_tac`x`
            \\ qexists_tac`value_st`
            \\ qexists_tac`value_num`
            \\ qexists_tac`value_state`
            \\ simp[])
    \\ simp[]
    \\ TRY (qpat_x_assum `INR _ = q` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `INR _ = q'` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `_ = r'` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `_ = r''` (SUBST_ALL_TAC o SYM))
    \\ simp[]
    \\ qpat_x_assum `_ = (q,r')` mp_tac
    \\ qpat_x_assum `_ = (q',r'')` mp_tac
    \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ TRY (MATCH_ACCEPT_TAC extcall_decoded_pair_cont_eq)
    \\ TRY (strip_tac \\ strip_tac \\ drule_all extcall_decoded_pair_cont_eq \\ simp[])
    \\ TRY (drule_all extcall_decoded_monad_owhile_eq \\ simp[])
    \\ TRY (drule_all extcall_result_owhile_eq \\ simp[])
    \\ TRY (drule_all extcall_decoded_pair_owhile_eq \\ simp[])
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[bind_def, return_def, raise_def, lift_sum_runtime_def]
    \\ strip_tac
    \\ strip_tac
    \\ TRY (qmatch_asmsub_rename_tac`case decoded of
              INL ret_val => (INL (Value ret_val),_)
            | INR e => (INR e,_)`
            \\ Cases_on`decoded` \\ gvs[cont_def])
    \\ TRY (drule_all extcall_decoded_tail_cont_eq \\ simp[])
    \\ TRY (drule_all extcall_decoded_monad_owhile_eq \\ simp[cont_def])
    \\ TRY (drule_all extcall_decoded_pair_owhile_eq \\ simp[cont_def])
    \\ TRY (drule_all extcall_decoded_tail_owhile_eq \\ simp[cont_def])
    \\ TRY (qpat_x_assum `INR _ = q'` (SUBST_ALL_TAC o SYM) \\ simp[])
    \\ TRY (drule_all extcall_run_success_empty \\ strip_tac)
    \\ TRY (irule extcall_value_full_default_owhile_eq \\ simp[])
    \\ TRY (drule_all extcall_value_full_default_owhile_eq \\ simp[])
    \\ TRY (simp[cont_def] \\ drule_all eval_expr_cps_owhile_result \\ simp[])
    \\ simp[]
    \\ TRY (qmatch_goalsub_abbrev_tac`eval_expr cx x'' final_st`
            \\ `eval_expr cx x'' final_st = (q',r'')` by (
                 qpat_x_assum `eval_expr cx x'' final_st = (q',r'')` ACCEPT_TAC)
            \\ qunabbrev_tac`final_st`)
    \\ TRY (drule_all extcall_result_owhile_eq \\ simp[])
    \\ TRY (drule_all extcall_decoded_pair_owhile_eq \\ simp[])
    \\ TRY (drule_all extcall_decoded_tail_owhile_eq \\ simp[])
    \\ TRY (qpat_x_assum `INL (INL _) = q` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `INL (INR _) = q` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `INR _ = q` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `INL _ = q'` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `INR _ = q'` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `_ = r'` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `_ = r''` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `_ = y'` (SUBST_ALL_TAC o SYM))
    \\ simp[]
    \\ TRY (qpat_x_assum `SOME _ = _` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `(SOME _,_) = _` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `get_accounts _ = _` mp_tac
            \\ simp[get_accounts_def] \\ strip_tac)
    \\ TRY (qpat_x_assum `get_transient_storage _ = _` mp_tac
            \\ simp[get_transient_storage_def] \\ strip_tac)
    \\ TRY (qpat_x_assum `(if ¬NULL _ then INL () else INR _) = INL _` mp_tac
            \\ simp[] \\ strip_tac)
    \\ TRY (drule_all extcall_value_arg_premise_refl \\ strip_tac)
    \\ TRY (drule_all extcall_value_arg_premise \\ strip_tac)
    \\ TRY (drule_all extcall_run_success_empty \\ strip_tac)
    \\ TRY (drule_all extcall_value_full_default_context_eq \\ simp[])
    \\ TRY (qmatch_asmsub_rename_tac`(case dest_AddressV (HD x) of
              NONE => raise (Error (TypeError "ExtCall target not address"))
            | SOME v => return v) addr_in = (INL target_addr,s_addr)`
            \\ qmatch_asmsub_rename_tac`(case dest_NumV (HD (TL x)) of
                  NONE => raise (Error (TypeError "ExtCall value not int"))
                | SOME v => return v) s_addr = (INL value_num,value_state)`
            \\ qmatch_asmsub_rename_tac`(case build_ext_calldata (get_tenv cx) fname atypes (SND (SOME value_num,TL (TL x))) of
                  NONE => raise (Error (RuntimeError "ExtCall build_calldata"))
                | SOME v => return v) value_state = (INL calldata,build_st)`
            \\ qmatch_asmsub_rename_tac`return build_st.accounts build_st = (INL accounts,accounts_st)`
            \\ qmatch_asmsub_rename_tac`return accounts_st.tStorage accounts_st = (INL tStorage,run_st)`
            \\ irule extcall_value_full_default_owhile_eq
            \\ simp[]
            \\ qexists_tac`accounts`
            \\ qexists_tac`atypes`
            \\ qexists_tac`build_st`
            \\ qexists_tac`calldata`
            \\ qexists_tac`fname`
            \\ qexists_tac`addr_in`
            \\ qexists_tac`run_st`
            \\ qexists_tac`s_addr`
            \\ qexists_tac`tStorage`
            \\ qexists_tac`target_addr`
            \\ qexists_tac`value_num`
            \\ qexists_tac`value_state`
            \\ qexists_tac`x`
            \\ simp[])
    \\ TRY (irule extcall_value_full_default_owhile_eq \\ simp[])
    \\ TRY (drule_all extcall_value_full_default_owhile_eq \\ simp[])
    \\ TRY (qpat_x_assum `return _ _ = _` mp_tac
            \\ simp[return_def] \\ strip_tac)
    \\ TRY (qpat_x_assum `return _ _ = _` mp_tac
            \\ simp[return_def] \\ strip_tac)
    \\ TRY (qmatch_asmsub_rename_tac`FST (SND (T,ret_data,ret_accounts,ret_tStorage)) = []`
            \\ `ret_data = []` by (first_x_assum mp_tac \\ simp[]))
    \\ TRY (qpat_x_assum `_.accounts = _` (SUBST_ALL_TAC o SYM))
    \\ TRY (qpat_x_assum `_.tStorage = _` (SUBST_ALL_TAC o SYM))
    \\ simp[]
    \\ TRY (qmatch_asmsub_rename_tac`(case dest_NumV (HD (TL x)) of
              NONE => raise (Error (TypeError "ExtCall value not int"))
            | SOME v => return v) value_st = (INL value_num,value_state)`
            \\ simp[cont_def]
            \\ irule extcall_value_default_owhile_eq
            \\ qexists_tac`x`
            \\ qexists_tac`value_st`
            \\ qexists_tac`value_num`
            \\ qexists_tac`value_state`
            \\ simp[])
    \\ TRY (drule_all extcall_value_default_owhile_eq \\ simp[])
    \\ TRY (drule_all extcall_value_default_owhile_from_arg_eq \\ simp[])
    \\ TRY (simp[cont_def]
            \\ qpat_x_assum `∀cx k. OWHILE _ stepk _ = _`
                 (qspecl_then[`cx`,`k`] ACCEPT_TAC))
    \\ simp[] )
  \\ conj_tac >- ( (* IntCall *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def,
       no_recursion_def]
    \\ BasicProvers.TOP_CASE_TAC
    \\ simp[cont_def]
    \\ reverse (Cases_on`q`)
    >- (qpat_x_assum `_ = (INR _,r)` mp_tac
        \\ simp[CaseEq"prod",CaseEq"sum",return_def]
        \\ strip_tac
        \\ simp[apply_exc_owhile_eq])
    \\ rename1`INL call_info`
    \\ PairCases_on`call_info`
    \\ ntac 3 (pop_assum mp_tac)
    \\ gvs[CaseEq"prod",CaseEq"sum",return_def]
    \\ rpt strip_tac
    \\ TRY (qpat_x_assum `_ = INL _` SUBST_ALL_TAC)
    \\ TRY (qpat_x_assum `_ = INL _` SUBST_ALL_TAC)
    \\ qpat_x_assum `∀s0 t0 s1 ts0 t1 s2 tup0 t2 s3 t3.
          check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL (),t0) ∧
          lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
          lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 =
            (INL tup0,t2) ∧
          type_check
            (LENGTH es ≤ LENGTH (FST (SND (SND tup0))) ∧
             LENGTH (FST (SND (SND tup0))) ≤ LENGTH es + LENGTH (FST (SND (SND (SND tup0)))))
            "IntCall args length" s3 = (INL (),t3) ⇒
          ∀st0 k0. cont (eval_exprs_cps cx es st0 k0) = _`
        (drule_then (drule_then drule))
    \\ simp_tac std_ss [cont_def] \\ disch_then drule
    \\ simp_tac std_ss [cont_def] \\ disch_then kall_tac
    \\ gvs[return_def]
      \\ CASE_TAC
      \\ reverse CASE_TAC
      >- gvs[return_def, raise_def, apply_exc_owhile_eq,
             Once OWHILE_THM, stepk_def, apply_exc_def]
      >> rw[Once OWHILE_THM, stepk_def, apply_vals_def]
      \\ drule eval_exprs_length \\ strip_tac
      \\ qpat_x_assum `∀s0 t0 s1 ts0 t1 s2 tup0 t2 s3 t3 s4 vs0 t4.
            _ ⇒ ∀st0 k0.
              cont (eval_exprs_cps (cx with stk updated_by CONS (src_id_opt,fn)) _ st0 k0) = _`
          (funpow 2 drule_then drule)
      \\ simp_tac std_ss []
      \\ disch_then $ drule_then drule \\ asm_simp_tac std_ss []
      \\ disch_then (fn th => PURE_ONCE_REWRITE_TAC [REWRITE_RULE[cont_def] th])
      \\ CASE_TAC
      \\ reverse CASE_TAC
      >- gvs[return_def, raise_def, apply_exc_owhile_eq,
             Once OWHILE_THM, stepk_def, apply_exc_def, o_DEF]
      \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, ignore_bind_def, LET_THM]
      (* after eval_exprs for defaults, now in IntCallK1: bind_arguments etc *)
      \\ gvs[CaseEq"prod", CaseEq"sum", return_def]
      \\ TRY (simp[apply_exc_def, o_DEF])
      \\ TRY (
        gvs[o_DEF]
        \\ rw[Once OWHILE_THM, SimpRHS, stepk_def]
        \\ CHANGED_TAC $ gvs[apply_exc_def]
        \\ gvs[o_DEF]
        \\ rw[Once OWHILE_THM])
      \\ qmatch_goalsub_abbrev_tac`pair_CASE prefix_res pc`
      \\ PairCases_on`prefix_res`
      \\ reverse (Cases_on`prefix_res0`)
      >- (qpat_x_assum `Abbrev ((INR y,prefix_res1) = _)`
            (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])
          \\ qpat_x_assum `(case _ of _ => _) = (INR y,prefix_res1)`
            (fn h =>
               assume_tac
                 (MATCH_MP intcall_prefix_error_eq h
                  handle HOL_ERR _ => MATCH_MP intcall_prefix_error_nolock_eq h))
          \\ gvs[Abbr`pc`, apply_exc_owhile_eq,
                  stepk_def, apply_exc_def, o_DEF]
          \\ once_rewrite_tac[OWHILE_THM]
          \\ simp[stepk_def, apply_exc_def, apply_exc_owhile_unfold_eq])
      \\ rename1`INL call_res`
      \\ qpat_x_assum `Abbrev ((_,prefix_res1) = _)`
           (fn th =>
              let val th' = REWRITE_RULE[markerTheory.Abbrev_def] th in
                assume_tac th' >> PURE_REWRITE_TAC [GSYM th']
              end)
      \\ qpat_x_assum `(_,prefix_res1) = _` (assume_tac o SYM)
      \\ TRY (
        qpat_x_assum `(case _ of _ => _) = (INR y,prefix_res1)`
          (fn h =>
             assume_tac
               (MATCH_MP intcall_prefix_error_eq h
                handle HOL_ERR _ => MATCH_MP intcall_prefix_error_nolock_eq h))
        \\ gvs[Abbr`pc`, apply_exc_owhile_eq,
                stepk_def, apply_exc_def, o_DEF])
      \\ TRY (qpat_x_assum `(case _ of _ => _) = (INL _,prefix_res1)`
        (fn h =>
           let
             val facts =
               MATCH_MP intcall_prefix_success_tup_facts_by_view h
               handle HOL_ERR _ =>
                 MATCH_MP intcall_nonview_prefix_success_tup_facts h
                 handle HOL_ERR _ =>
                   MATCH_MP intcall_prefix_success_tup_facts h
                   handle HOL_ERR _ => MATCH_MP intcall_prefix_success_nolock_tup_facts h
           in
             strip_assume_tac facts
           end))
      \\ Cases_on `cx.nonreentrant_slot`
      \\ TRY (
        qpat_x_assum `(case NONE of _ => _ | _ => _) _ = (INL (),_)` mp_tac
        \\ simp[raise_def, return_def])
      \\ simp[raise_def, return_def]
      \\ qmatch_asmsub_rename_tac`eval_exprs _ (DROP _ _) _ = (INL dflt_vals,dflt_st)`
      \\ qmatch_asmsub_abbrev_tac`check (¬MEM src_fn cx.stk) "recursion" st = _`
      \\ TRY (qpat_x_assum `call_res = _` SUBST_ALL_TAC)
      \\ TRY (qpat_x_assum `lift_option_type (bind_arguments _ _ _) _ _ = _`
           (fn th => assume_tac th >> PURE_REWRITE_TAC [th]))
      \\ TRY (qpat_x_assum `get_scopes _ = _`
           (fn th => assume_tac th >> PURE_REWRITE_TAC [th]))
      \\ TRY (qpat_x_assum `lift_option_type (evaluate_type _ _) _ _ = _`
           (fn th => assume_tac th >> PURE_REWRITE_TAC [th]))
      \\ TRY (qpat_x_assum `(case SOME _ of _ => _ | _ => _) _ = _`
           (fn th => assume_tac th >> PURE_REWRITE_TAC [th]))
      \\ TRY (qpat_x_assum `push_function _ _ _ _ = _`
           (fn th => assume_tac th >> PURE_REWRITE_TAC [th]))
      \\ simp[bind_def, ignore_bind_def, return_def, raise_def]
      \\ TRY (simp[Abbr`pc`, o_DEF])
      \\ rw[return_def, finally_def, try_def, bind_def]
      \\ simp[o_DEF]
      (* Fire eval_stmts IH where this is the successful-call branch. *)
      \\ last_x_assum (funpow 2 drule_then drule)
      \\ asm_simp_tac std_ss [return_def]
      \\ fs[]
      \\ strip_tac
      \\ FIRST [
        qpat_x_assum
          `∀s8 t3 s9 vs0 t4 s10 dflt_vs0 t5 s11 env0 t6 s12 prev0 t7
             s13 rtv0 t8 s15 cx0 t10 st0 k0.
             _ ⇒ cont (eval_stmts_cps _ _ _ _) = _`
          drule_all
        \\ disch_then (fn th => PURE_REWRITE_TAC [REWRITE_RULE[cont_def] th]),
        qpat_x_assum
          `∀s8 t3 s9 vs0 t4 s10 dflt_vs0 t5 s11 env0 t6 s12 prev0 t7
             s13 rtv0 t8 s14 t9 s15 cx0 t10 st0 k0.
             _ ⇒ cont (eval_stmts_cps _ _ _ _) = _`
          drule_all
        \\ disch_then (fn th => PURE_REWRITE_TAC [REWRITE_RULE[cont_def] th]),
        ALL_TAC]
      (* Derive context facts from push_function where available. *)
      \\ TRY (
        qpat_x_assum `push_function _ _ _ _ = _` mp_tac
        \\ simp[push_function_def, return_def]
        \\ strip_tac \\ gvs[])
      \\ TRY (
        qpat_x_assum `(case _ of _ => _) = (INR y,prefix_res1)`
          (fn th => assume_tac th >> PURE_REWRITE_TAC [th])
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def, o_DEF,
              apply_exc_owhile_unfold_eq])
      \\ TRY (
        qpat_x_assum `(case _ of _ => _) = (INL _,prefix_res1)`
          (mp_tac o MATCH_MP intcall_prefix_success_missing_slot_raise_eq)
        \\ simp[])
      (* Case split on eval_stmts result *)
      \\ TRY CASE_TAC \\ TRY CASE_TAC
      \\ rw[Once OWHILE_THM, stepk_def]
      (* Success/exception: apply IntCallK2 finalizers. *)
      \\ TRY (simp[intcall_k2_apply_success_eq])
      \\ TRY (simp[intcall_k2_apply_success_view_eq])
      \\ TRY (simp[intcall_k2_apply_success_nolock_eq])
      \\ TRY (simp[intcall_k2_apply_exc_eq])
      \\ TRY (simp[intcall_k2_apply_exc_view_eq])
      \\ TRY (simp[intcall_k2_apply_exc_nolock_eq])
      \\ rw[apply_exc_def, o_DEF, liftk1, bind_def, ignore_bind_def,
            finally_def, return_def]
      \\ simp[pop_function_def, set_scopes_def, return_def, raise_def]
      \\ simp[option_CASE_rator, sum_CASE_rator]
    \\ rw[] )
  (* ===== Chain interaction builtins ===== *)
  (* All 5 new cases: CPS eval_exprs then continuation matches big-step body.
     Pattern: unfold both sides, use IH for eval_exprs, match continuation bodies. *)
  (* Chain interaction builtins: all use same tactic.
     CPS evals exprs then calls apply_vals which matches big-step body. *)
  \\ rpt (conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[]
    \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def]))
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def] (* eval_exprs [] *)
  (* eval_exprs (e::es) *)
  \\ rw[eval_expr_cps_def, evaluate_def, bind_def]
  \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
  \\ CASE_TAC \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_val_def]
  \\ first_x_assum (drule_then drule) \\ rw[]
  \\ CASE_TAC \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  \\ rw[return_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_vals_def]
  >> rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_vals_def]
  \\ gvs[apply_vals_def]
  \\ rw[Once OWHILE_THM, stepk_def]
QED

Definition fromk_def[simp]:
  fromk (SOME (AK cx Apply st DoneK)) = (INL (), st) ∧
  fromk (SOME (AK cx (ApplyExc ex) st DoneK)) = (INR ex, st) ∧
  fromk _ = (INR $ Error (TypeError "fromk"), empty_state)
End

val () = cv_trans fromk_def;

Theorem cont_tr:
  cont ak = if nextk ak = DoneK then SOME ak else cont (stepk ak)
Proof
  simp[Once cont_def]
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC \\ gs[]
  \\ simp[Once cont_def]
QED

val cont_tr_pre_def = cv_trans_pre "cont_pre" cont_tr;

Theorem IS_SOME_cont:
  IS_SOME (cont ak) ⇔
  ∃n. nextk (FUNPOW stepk n ak) = DoneK
Proof
  rw[cont_def, OWHILE_def]
QED

Theorem cont_pre_IS_SOME_cont:
  cont_pre ak ⇔ IS_SOME (cont ak)
Proof
  EQ_TAC
  >- (
    qid_spec_tac`ak`
    \\ ho_match_mp_tac (theorem "cont_pre_ind")
    \\ rw[cont_def, OWHILE_def] \\ gs[]
    >- (
      first_x_assum(qspec_then`SUC n`mp_tac)
      \\ rw[FUNPOW] )
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[] )
  \\ rw[IS_SOME_cont]
  \\ pop_assum mp_tac
  \\ qid_spec_tac`ak`
  \\ Induct_on`n` \\ rw[]
  >- rw[cont_tr_pre_def]
  \\ rw[Once cont_tr_pre_def]
  \\ first_x_assum irule
  \\ gs[FUNPOW]
QED

Theorem eval_stmts_eq_cont_cps:
  eval_stmts cx body st = fromk $ cont (eval_stmts_cps cx body st DoneK)
Proof
  Cases_on`eval_stmts cx body st`
  \\ qmatch_goalsub_rename_tac`res,st1`
  \\ qspecl_then[`cx`,`body`,`st`,`DoneK`]mp_tac(cj 2 eval_cps_eq)
  \\ simp[cont_def] \\ strip_tac
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC
  >- (Cases_on `res` \\ gvs[])
  \\ CASE_TAC \\ simp[]
QED

Definition fromtvk_def:
  fromtvk (SOME (AK cx (ApplyTv tv) st DoneK)) = (INL tv, st) ∧
  fromtvk (SOME (AK cx (ApplyExc ex) st DoneK)) = (INR ex, st) ∧
  fromtvk _ = (INR $ Error (TypeError "fromtvk"), empty_state)
End

val () = cv_auto_trans fromtvk_def;

Theorem eval_expr_eq_cont_cps:
  eval_expr cx e st = fromtvk $ cont (eval_expr_cps cx e st DoneK)
Proof
  Cases_on`eval_expr cx e st`
  \\ qmatch_goalsub_rename_tac`res,st1`
  \\ qspecl_then[`cx`,`e`,`st`,`DoneK`]mp_tac(cj 8 eval_cps_eq)
  \\ simp[cont_def] \\ strip_tac
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC
  \\ Cases_on `res` \\ gvs[]
  \\ simp[fromtvk_def]
QED

val constants_env_pre_def = constants_env_def
  |> SRULE [eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "constants_env_pre";

Theorem constants_env_pre[cv_pre]:
  ∀v0 v1 v2 v3 v acc. constants_env_pre v0 v1 v2 v3 v acc
Proof
  ho_match_mp_tac constants_env_ind
  \\ rw[]
  \\ rw[Once constants_env_pre_def]
  \\ gs[eval_expr_eq_cont_cps]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_expr_cps ec ee es dk`
  \\ qspecl_then[`ec`,`ee`,`es`,`dk`]mp_tac $ cj 8 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC
  \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM, Abbr`dk`]
QED

val evaluate_defaults_pre_def = evaluate_defaults_def
  |> SRULE [eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "evaluate_defaults_pre";

Theorem evaluate_defaults_pre[cv_pre]:
  ∀cx am v. evaluate_defaults_pre cx am v
Proof
  ntac 2 gen_tac
  \\ Induct \\ rw[]
  \\ rw[Once evaluate_defaults_pre_def]
  \\ gs[eval_expr_eq_cont_cps]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_expr_cps ec ee es dk`
  \\ qspecl_then[`ec`,`ee`,`es`,`dk`]mp_tac $ cj 8 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC
  \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM, Abbr`dk`]
QED

val call_external_function_pre_def = call_external_function_def
     |> SRULE [eval_stmts_eq_cont_cps,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, COND_RATOR, option_CASE_rator,
               get_transient_storage_def, update_transient_def]
     |> cv_auto_trans_pre "call_external_function_pre";

Theorem call_external_function_pre[cv_pre]:
  call_external_function_pre am cx nr mut ts all_mods args dflts vals
    (bod:stmt list) ret
Proof
  rw[call_external_function_pre_def]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_stmts_cps cx ss st k`
  \\ qspecl_then[`cx`,`ss`,`st`,`k`]mp_tac $ cj 2 eval_cps_eq
  \\ rw[]
  \\ CASE_TAC
  \\ CASE_TAC
  \\ rw[Abbr`k`, cont_def]
  \\ rw[Once OWHILE_THM]
QED

val () = cv_auto_trans call_external_def;

val () = cv_auto_trans load_contract_def;
