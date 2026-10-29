Theory vyperSmallStep
Ancestors
  arithmetic combin pair list While
  vyperMisc vyperNsidFmap vyperValue vyperContext vyperState vyperCreate vyperInterpreter vyperABI
  vyperCallOutcome[ignore_grammar]
Libs
  cv_transLib wordsLib

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
  | CustomErrorK identifier (type list) eval_continuation
  | LogK nsid eval_continuation
  | PopK eval_continuation
  | AppendK expr eval_continuation
  | AppendK1 place eval_continuation
  | AnnAssignK identifier type_value eval_continuation
  | AssignK base_assignment_target eval_continuation
  | AssignK1 eval_result eval_continuation
  | TupleAssignK (assignment_target list) eval_continuation
  | TupleStoreK value eval_continuation
  | TupleStoresK (assignment_target list) (value list) eval_continuation
  | AugAssignK type binop expr eval_continuation
  | AugAssignK1 type place type_value value binop eval_continuation
  | BasePlaceSubscriptK expr eval_continuation
  | BasePlaceSubscriptK1 eval_result eval_continuation
  | BasePlaceAttributeK identifier eval_continuation
  | TargetPlaceK eval_continuation
  | IfK (stmt list) (stmt list) eval_continuation
  | IfK1 eval_result (stmt list) (stmt list) eval_continuation
  | IfK2 eval_continuation
  | ForK identifier type_value num (stmt list) eval_continuation
  | ForK1 type_value identifier (stmt list) (value list) eval_continuation
  | ExprK eval_continuation
  | StmtsK (stmt list) eval_continuation
  | ArrayK type eval_continuation
  | RangeK1 expr eval_continuation
  | RangeK2 value eval_continuation
  | IfExpK expr expr eval_continuation
  | ConditionalK eval_continuation
  | StructLitK (identifier list) eval_continuation
  | SubscriptK type expr eval_continuation
  | SubscriptK1 type eval_result eval_continuation
  | AttributeK type identifier eval_continuation
  | BuiltinK type builtin (type list) eval_continuation
  | LenK eval_continuation
  | TypeBuiltinK type_builtin type (type list) eval_continuation
  | CallSendK bool eval_continuation
  | ExtTargetK bool bool ext_call_sig ext_call_opts (expr list) eval_continuation
  | ExtArgsK bool bool ext_call_sig ext_call_opts (value list) (expr list) eval_continuation
  | ExtKwargsK bool bool ext_call_sig ext_call_opts (value list) (eval_result list) eval_continuation
  (* Chain interaction builtin continuations *)
  | RawCallK type raw_call_flags eval_continuation
  | RawCallCalldataK raw_call_flags eval_continuation
  | RawLogK eval_continuation
  | RawRevertK eval_continuation
  | SelfDestructK eval_continuation
  | CreateK (type list) create_kind bool bool (num option) eval_continuation
  | BlueprintPrefixK (type list) create_kind bool bool (expr list) eval_continuation
  | BlueprintSuffixK (value list) eval_continuation
  | RawCreatePrefixK (type list) bool bool (expr list) eval_continuation
  | RawCreateArgsK (value list) (expr list) eval_continuation
  | RawCreateSaltK (value list) (value list) eval_continuation
  | ReadResultsK eval_continuation
  | IntCallK (nsid |-> type_args) nsid ((identifier # type) list) (expr list) type (stmt list) bool function_mutability eval_continuation
  | IntCallK1 (nsid |-> type_args) nsid ((identifier # type) list) (eval_result list) (scope list) type (stmt list) bool function_mutability eval_continuation
  | IntCallK2 (scope list) type_value bool bool eval_continuation
  | ExprsK (expr list) eval_continuation
  | ExprsK1 value eval_continuation
  | ExprResultsK (expr list) eval_continuation
  | ExprResultsK1 eval_result eval_continuation
  | DoneK
End

Datatype:
  apply_base_continuation
  = Apply
  | ApplyExc exception
  | ApplyTv eval_result
  | ApplyVal value
  | ApplyVals (value list)
  | ApplyResults (eval_result list)
  | ApplyPlace place
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

Triviality list_size_take_bound:
  ∀es n. list_size expr_size (TAKE n es) ≤ list_size expr_size es
Proof
  Induct >> Cases_on `n` >> simp[]
QED

Definition eval_base_place_cps_def:
  eval_base_place_cps cx (NameTarget id) st k =
    liftk cx ApplyTv (do
      sc <- get_scopes;
      type_check (IS_SOME (lookup_scopes id sc)) "NameTarget not in scope";
      return (PlaceR (MemoryPlace id [])) od st) k /\
  eval_base_place_cps cx (TopLevelNameTarget (src,id)) st k =
    liftk cx ApplyTv (lookup_global cx src id st) k /\
  eval_base_place_cps cx (AttributeTarget t id) st k =
    eval_base_place_cps cx t st (BasePlaceAttributeK id k) /\
  eval_base_place_cps cx (SubscriptTarget t e) st k =
    eval_base_place_cps cx t st (BasePlaceSubscriptK e k)
End
val () = eval_base_place_cps_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition eval_target_place_cps_def:
  eval_target_place_cps cx t st k =
    eval_base_place_cps cx t st (TargetPlaceK k)
End
val () = cv_auto_trans eval_target_place_cps_def;

Definition eval_expr_cps_def:
  eval_expr_cps cx1 (Name _ id) st k =
    liftk cx1 ApplyTv
      (do sc <- get_scopes;
          type_check (IS_SOME (lookup_scopes id sc)) "Name not in scope";
          return (PlaceR (MemoryPlace id [])) od st) k ∧
  eval_expr_cps cx2 (TopLevelName _ (src_id_opt, id)) st k =
    liftk cx2 ApplyTv (lookup_global cx2 src_id_opt id st) k ∧
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
    eval_expr_cps cx7 e st (AttributeK (expr_type e) id k) ∧
  eval_expr_cps cx8 (Builtin ty bt es) st k =
    (case type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st of
       (INR ex, st) => AK cx8 (ApplyExc ex) st k
     | (INL (), st) => if bt = Len then eval_expr_cps cx8 (HD es) st (LenK k)
                       else eval_exprs_cps cx8 es st (BuiltinK ty bt (MAP expr_type es) k)) ∧
  eval_expr_cps cx8 (Pop _ bt) st k =
    eval_target_place_cps cx8 bt st (PopK k) ∧
  eval_expr_cps cx8 (TypeBuiltin _ tb typ es) st k =
    (case type_check (type_builtin_args_length_ok tb (LENGTH es))
            "TypeBuiltin args" st of
        (INR ex, st) => AK cx8 (ApplyExc ex) st k
      | (INL tv, st) => eval_exprs_cps cx8 es st (TypeBuiltinK tb typ (MAP expr_type es) k)) ∧
  eval_expr_cps cx9 (Call _ (Send has_gas) es _) st k =
    (case type_check (LENGTH es = if has_gas then 3 else 2) "Send args" st of
       (INR ex, st) => AK cx9 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx9 es st (CallSendK has_gas k)) ∧
  eval_expr_cps cx10 (Call _ (ExtCall is_static skip_check sig opts) es _) st k =
    eval_exprs_cps cx10 (TAKE 1 es) st
      (ExtTargetK is_static skip_check sig opts (DROP 1 es) k) ∧
  (* Chain interaction builtins *)
  eval_expr_cps cx10 (Call ty (RawCallTarget flags) es _) st k =
    eval_exprs_cps cx10 es st (RawCallK ty flags k) ∧
  eval_expr_cps cx10 (Call ty (RawCallCalldataTarget flags) es _) st k =
    eval_exprs_cps cx10 es st (RawCallCalldataK flags k) ∧
  eval_expr_cps cx10 (Call _ RawLog es _) st k =
    eval_exprs_cps cx10 es st (RawLogK k) ∧
  eval_expr_cps cx10 (Call _ RawRevert es _) st k =
    eval_exprs_cps cx10 es st (RawRevertK k) ∧
  eval_expr_cps cx10 (Call _ SelfDestructTarget es _) st k =
    eval_exprs_cps cx10 es st (SelfDestructK k) ∧
  eval_expr_cps cx10 (Call ty (CreateTarget kind has_salt rof) es _) st k =
    (case kind of
       CreateFromBlueprint raw_args =>
         eval_exprs_cps cx10 (TAKE (if has_salt then 4 else 3) es) st
           (BlueprintPrefixK (MAP expr_type es) kind has_salt rof
             (DROP (if has_salt then 4 else 3) es) k)
     | RawCreate =>
         eval_exprs_cps cx10 (TAKE 2 es) st
           (RawCreatePrefixK (MAP expr_type es) has_salt rof (DROP 2 es) k)
     | _ => eval_exprs_cps cx10 es st
         (CreateK (MAP expr_type es) kind has_salt rof NONE k)) ∧
  eval_expr_cps cx10 (Call _ (IntCall (ns, fn)) es _) st k =
    (case do
      type_check (no_recursion (ns, fn) cx10.stk) "recursion";
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
          eval_expr_results_cps cx10 es st (IntCallK all_tenv (ns, fn) args dflts ret body nr mut k)) ∧
  eval_exprs_cps cx11 [] st k = AK cx11 (ApplyVals []) st k ∧
  eval_exprs_cps cx12 (e::es) st k =
    eval_expr_cps cx12 e st (ExprsK es k) ∧
  eval_expr_results_cps cx [] st k = AK cx (ApplyResults []) st k ∧
  eval_expr_results_cps cx (e::es) st k =
    eval_expr_cps cx e st (ExprResultsK es k)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (cx,e,st,k) => expr_size e
    | INR (INL (cx,es,st,k)) => list_size expr_size es
    | INR (INR (cx,es,st,k)) => list_size expr_size es)’
  \\ rw[list_size_SUM_MAP, MAP_MAP_o, ETA_AX,
        list_size_pair_size_map, builtin_args_length_ok_def, check_def, type_check_def,
        assert_def, LENGTH_EQ_NUM_compute] \\ rw[]
  \\ qmatch_goalsub_abbrev_tac `TAKE n es`
  \\ qspecl_then [`es`, `n`] mp_tac list_size_take_bound
  \\ pure_rewrite_tac [list_size_SUM_MAP]
  \\ simp[Abbr `n`]
  \\ strip_tac \\ decide_tac
End

val eval_expr_cps_pre_def = eval_expr_cps_def
   |> SRULE
        [liftk1, bind_def, ignore_bind_def,
         LET_RATOR, option_CASE_rator,
         sum_CASE_rator, prod_CASE_rator, lift_option_def]
   |> cv_auto_trans_pre "eval_expr_cps_pre eval_exprs_cps_pre eval_expr_results_cps_pre";

Theorem eval_expr_cps_pre[cv_pre]:
  (∀a b c d. eval_expr_cps_pre a b c d) ∧
  (∀x y z w. eval_exprs_cps_pre x y z w) ∧
  (∀x y z w. eval_expr_results_cps_pre x y z w)
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

Definition assign_tuple_targets_cps_def:
  assign_tuple_targets_cps cx (BaseTarget t) v st k =
    eval_target_place_cps cx t st (TupleStoreK v k) /\
  assign_tuple_targets_cps cx (TupleTarget gs) v st k =
    (case v of
       ArrayV (TupleV vs) => assign_tuple_target_list_cps cx gs vs st k
     | _ => AK cx (ApplyExc (Error (TypeError "TupleTarget value"))) st k) /\
  assign_tuple_target_list_cps cx [] [] st k = AK cx Apply st k /\
  assign_tuple_target_list_cps cx (g::gs) (v::vs) st k =
    assign_tuple_targets_cps cx g v st (TupleStoresK gs vs k) /\
  assign_tuple_target_list_cps cx gs vs st k =
    AK cx (ApplyExc (Error (TypeError "TupleTarget length"))) st k
End
val () = cv_auto_trans assign_tuple_targets_cps_def;

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
  eval_stmt_cps cx (Raise (RaiseCustomError err)) st k =
    (case err of CustomError id positional kwargs =>
       case get_module_code cx (FST id) of
       | NONE => AK cx
           (ApplyExc $ Error (RuntimeError "custom error declaration")) st k
       | SOME tops =>
           case lookup_custom_error_args_in (SND id) tops of
           | NONE => AK cx
               (ApplyExc $ Error (RuntimeError "custom error declaration")) st k
           | SOME params =>
               case order_custom_error_args params err of
               | NONE => AK cx
                   (ApplyExc $ Error (RuntimeError "custom error arguments")) st k
               | SOME es =>
                   eval_exprs_cps cx es st
                     (CustomErrorK (SND id) (MAP SND params) k)) ∧
  eval_stmt_cps cx (Assert e reason) st k =
    eval_expr_cps cx e st (AssertK reason k) ∧
  eval_stmt_cps cx (Log id es) st k = eval_exprs_cps cx es st (LogK id k) ∧
  eval_stmt_cps cx (AnnAssign id typ e) st k =
    (case evaluate_type (get_tenv cx) typ of
       NONE => AK cx (ApplyExc (Error (TypeError "AnnAssign evaluate_type"))) st k
     | SOME tyv => eval_expr_cps cx e st (AnnAssignK id tyv k)) ∧
  eval_stmt_cps cx (Append t e) st k =
    eval_target_place_cps cx t st (AppendK e k) ∧
  eval_stmt_cps cx (Assign (BaseTarget t) e) st k =
    eval_expr_cps cx e st (AssignK t k) ∧
  eval_stmt_cps cx (Assign (TupleTarget gs) e) st k =
    eval_expr_cps cx e st (TupleAssignK gs k) ∧
  eval_stmt_cps cx (AugAssign ty t bop e) st k =
    eval_target_place_cps cx t st (AugAssignK ty bop e k) ∧
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
  apply cx st (TupleStoresK gs vs k) =
    assign_tuple_target_list_cps cx gs vs st k /\
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
  apply cx st (IfK1 tv ss1 ss2 k) =
    (case read_result cx tv st of
       (INR ex,st1) => AK cx (ApplyExc ex) st1 (IfK2 k)
     | (INL v,st1) =>
         case v of
           BoolV b => eval_stmts_cps cx (if b then ss1 else ss2) st1 (IfK2 k)
         | _ => AK cx (ApplyExc (Error (TypeError "not BoolV"))) st1 (IfK2 k)) ∧
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
  apply_exc cx ex st (CustomErrorK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (LogK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AnnAssignK _ _ k) = AK cx (ApplyExc ex) st k ∧  (* id, tyv unused *)
  apply_exc cx ex st (AssignK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssignK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK1 _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TupleAssignK _ k) = AK cx (ApplyExc ex) st k /\
  apply_exc cx ex st (TupleStoreK _ k) = AK cx (ApplyExc ex) st k /\
  apply_exc cx ex st (TupleStoresK _ _ k) = AK cx (ApplyExc ex) st k /\
  apply_exc cx ex st (BasePlaceSubscriptK _ k) = AK cx (ApplyExc ex) st k /\
  apply_exc cx ex st (BasePlaceSubscriptK1 _ k) = AK cx (ApplyExc ex) st k /\
  apply_exc cx ex st (BasePlaceAttributeK _ k) = AK cx (ApplyExc ex) st k /\
  apply_exc cx ex st (TargetPlaceK k) = AK cx (ApplyExc ex) st k ∧
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
  apply_exc cx ex st (ConditionalK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfExpK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StructLitK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK1 _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (PopK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BuiltinK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (LenK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TypeBuiltinK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CallSendK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExtTargetK _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExtArgsK _ _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExtKwargsK _ _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawCallK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawCallCalldataK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawLogK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawRevertK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SelfDestructK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CreateK _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BlueprintPrefixK _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BlueprintSuffixK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawCreatePrefixK _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawCreateArgsK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawCreateSaltK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ReadResultsK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK _ _ _ _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK1 _ _ _ _ prev _ _ _ _ k) =
    liftk (cx with stk updated_by TL) (K (ApplyExc ex)) (set_scopes prev st) k ∧
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
  apply_exc cx ex st (ExprResultsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExprResultsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st DoneK = AK cx (ApplyExc ex) st DoneK
End

val () = apply_exc_def
  |> SRULE [finally_def, bind_def, ignore_bind_def,
            liftk1, prod_CASE_rator, sum_CASE_rator,
            COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

Definition apply_place_def:
  apply_place cx p st (AppendK e k) =
    eval_expr_cps cx e st (AppendK1 p k) /\
  apply_place cx p st (PopK k) =
    liftk cx ApplyTv (pop_place cx p st) k /\
  apply_place cx p st (AssignK1 pv k) =
    liftk cx (K Apply) (do
      v <- read_result cx pv;
      write_place cx p v od st) k /\
  apply_place cx p st (TupleStoreK v k) =
    liftk cx (K Apply) (write_place cx p v st) k /\
  apply_place cx p st (AugAssignK ty bop e k) =
    (case (do
       cur <- read_place cx p;
       ptv <- place_type_value cx p;
       return (ptv,cur) od st) of
       (INL (ptv,cur),st1) => eval_expr_cps cx e st1 (AugAssignK1 ty p ptv cur bop k)
     | (INR ex,st1) => AK cx (ApplyExc ex) st1 k) /\
  apply_place cx p st DoneK = AK cx (ApplyPlace p) st DoneK /\
  apply_place cx p st _ =
    AK cx (ApplyExc (Error (TypeError "apply_place k"))) st DoneK
End
val () = apply_place_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_tv_def:
  apply_tv cx tv st (ExprResultsK es k) =
    eval_expr_results_cps cx es st (ExprResultsK1 tv k) /\
  apply_tv cx tv st (AssignK t k) =
    eval_target_place_cps cx t st (AssignK1 tv k) /\
  apply_tv cx tv st (BasePlaceSubscriptK e k) =
    eval_expr_cps cx e st (BasePlaceSubscriptK1 tv k) /\
  apply_tv cx tv st (BasePlaceAttributeK id k) =
    liftk cx ApplyTv (extend_place cx tv (AttrSubscript id) st) k /\
  apply_tv cx tv st (TargetPlaceK k) =
    liftk cx ApplyPlace (get_place tv st) k /\
  apply_tv cx tv st (ConditionalK k) =
    liftk cx ApplyTv (conditional_result cx tv st) k /\
  apply_tv cx tv st (AttributeK ty id k) =
    liftk cx ApplyTv (select_result cx ty tv (AttrSubscript id) st) k /\
  apply_tv cx tv st (TupleAssignK gs k) =
    liftk cx ApplyVal (read_result cx tv st) (TupleAssignK gs k) /\
  apply_tv cx tv st (SubscriptK arr_typ e k) =
    eval_expr_cps cx e st (SubscriptK1 arr_typ tv k) ∧
  apply_tv cx tv st (IfK ss1 ss2 k) =
    liftk cx (K Apply) (push_scope st) (IfK1 tv ss1 ss2 k) ∧
  apply_tv cx tv st (LenK k) =
    liftk cx ApplyTv (do
      len <- result_array_length cx tv;
      return $ Value $ IntV (&len)
    od st) k ∧
  apply_tv cx tv st (ExprK k) =
    (case type_check (¬is_HashMapRef tv) "Expr HashMapRef" st of
       (INR ex, st) => apply_exc cx ex st k
     | (INL (), st) => apply cx st k) ∧
  apply_tv cx tv st (ReturnK k) =
    liftk cx ApplyVal (read_result cx tv st) (ReturnK k) ∧
  apply_tv cx tv st (AnnAssignK id tyv k) =
    liftk cx ApplyVal (read_result cx tv st) (AnnAssignK id tyv k) ∧
  apply_tv cx tv st (AppendK1 btv k) =
    liftk cx ApplyVal (read_result cx tv st) (AppendK1 btv k) ∧

  apply_tv cx tv st (ArrayK arr_typ k) =
    liftk cx ApplyVal (read_result cx tv st) (ArrayK arr_typ k) ∧
  apply_tv cx tv st (ExprsK es k) =
    liftk cx ApplyVal (read_result cx tv st) (ExprsK es k) ∧
  apply_tv cx tv st DoneK = AK cx (ApplyTv tv) st DoneK ∧
  apply_tv cx tv st k =
    liftk cx ApplyVal (read_result cx tv st) k
End

val () = apply_tv_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

(* ===== apply_val helpers: extracted complex do-block clauses so each
        translates cheaply on its own (cv_trans speed) ===== *)
Definition apply_val_array_def:
  apply_val_array cx arr_typ v st k =
    (case evaluate_type (get_tenv cx) arr_typ of
     | SOME arr_tv =>
         liftk cx ApplyVals
           (lift_option_type (extract_elements arr_tv v) "For not ArrayV" st) k
     | NONE => AK cx (ApplyExc (Error (TypeError "For array type"))) st k)
End
val () = apply_val_array_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
            lift_option_type_def]
  |> cv_auto_trans;
Definition apply_val_range2_def:
  apply_val_range2 cx v1 v2 st k =
    (case do rl <- lift_sum $ get_range_limits v1 v2;
             n1 <<- FST rl; n2 <<- SND rl;
             return $ GENLIST (λn. IntV (n1 + &n)) n2
     od st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL vs, st) => AK cx (ApplyVals vs) st k)
End
val () = apply_val_range2_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
            LET_RATOR, lift_sum_def, bind_def, ignore_bind_def]
  |> cv_auto_trans;
Definition apply_val_subscript_def:
  apply_val_subscript cx arr_typ tv1 v2 st k =
    liftk cx ApplyTv
      (select_result cx arr_typ tv1 (ValueSubscript v2) st) k
End
val () = apply_val_subscript_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;
Definition apply_val_def:
  apply_val cx v st (ReturnK k) = apply_exc cx (ReturnException v) st k ∧
  apply_val cx v st (AssertK r k) =
    (case v of
       BoolV T => apply cx st k
     | BoolV F =>
        (case r of
           AssertBare => apply_exc cx (AssertException "") st k
         | AssertUnreachable => apply_exc cx (AssertException "UNREACHABLE") st k
         | AssertReason se => eval_expr_cps cx se st (RaiseK k)
         | AssertCustomError err =>
             (case err of CustomError id positional kwargs =>
                case get_module_code cx (FST id) of
                | NONE => apply_exc cx
                    (Error (RuntimeError "custom error declaration")) st k
                | SOME tops =>
                    case lookup_custom_error_args_in (SND id) tops of
                    | NONE => apply_exc cx
                        (Error (RuntimeError "custom error declaration")) st k
                    | SOME params =>
                        case order_custom_error_args params err of
                        | NONE => apply_exc cx
                            (Error (RuntimeError "custom error arguments")) st k
                        | SOME es =>
                            eval_exprs_cps cx es st
                              (CustomErrorK (SND id) (MAP SND params) k)))
     | _ => apply_exc cx (Error (TypeError "not BoolV")) st k) ∧
  apply_val cx v st (RaiseK k) =
    (case v of
       StringV str => apply_exc cx (AssertException str) st k
     | _ => apply_exc cx (Error (TypeError "not StringV")) st k) ∧
  apply_val cx v st (AnnAssignK id tyv k) =
    liftk cx (K Apply) (new_variable id tyv v st) k ∧
  apply_val cx v st (TupleAssignK gs k) =
    assign_tuple_targets_cps cx (TupleTarget gs) v st k /\
  apply_val cx v st (BasePlaceSubscriptK1 pv k) =
    liftk cx ApplyTv (extend_place cx pv (ValueSubscript v) st) k /\
  apply_val cx v st (AugAssignK1 ty p ptv cur bop k) =
    liftk cx (K Apply) (do
      u <<- (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0);
      res <- lift_sum (evaluate_binop u ptv bop cur v);
      write_place cx p res od st) k ∧
  apply_val cx v st (AppendK1 p k) =
    liftk cx (K Apply) (append_place cx p v st) k ∧
  apply_val cx v st (ArrayK arr_typ k) = apply_val_array cx arr_typ v st k ∧
  apply_val cx v st (RangeK1 e k) = eval_expr_cps cx e st (RangeK2 v k) ∧
  apply_val cx v2 st (RangeK2 v1 k) = apply_val_range2 cx v1 v2 st k ∧
  apply_val cx v st (IfExpK e2 e3 k) =
    (case v of
       BoolV T => eval_expr_cps cx e2 st (ConditionalK k)
     | BoolV F => eval_expr_cps cx e3 st (ConditionalK k)
     | _ => apply_exc cx (Error (TypeError "not BoolV")) st k) ∧
  apply_val cx v2 st (SubscriptK1 arr_typ tv1 k) =
    apply_val_subscript cx arr_typ tv1 v2 st k ∧
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
      | (INL vs, st) => eval_for_cps cx tyv id body vs st k) ∧
  apply_vals cx vs st (StructLitK ks k) =
    apply_tv cx (Value $ StructV (ZIP (ks, vs))) st k ∧
  apply_vals cx vs st (BuiltinK ty bt tys k) =
    liftk cx ApplyTv (do
      acc <- get_accounts;
      v <- lift_sum $ evaluate_builtin cx acc ty bt tys vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (TypeBuiltinK tb typ tys k) =
    liftk cx ApplyTv (do
      v <- lift_sum $ evaluate_type_builtin cx tb typ tys vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (LogK id k) =
    liftk cx (K Apply) (do
      event <- lift_option
        (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
        "Log encode event";
      push_log event
    od st) k ∧
  apply_vals cx vs st (CustomErrorK error_name arg_types k) =
    (case build_custom_error_data (get_tenv cx) error_name arg_types vs of
     | NONE => apply_exc cx (Error (RuntimeError "custom error encoding")) st k
     | SOME data => apply_exc cx (Error (RevertData data)) st k) ∧
  apply_vals cx vs st (CallSendK has_gas k) =
    liftk cx ApplyTv (eval_send cx has_gas vs st) k ∧
  apply_vals cx target st (ExtTargetK is_static skip_check sig opts es k) =
    eval_expr_results_cps cx (TAKE (LENGTH (FST (SND sig))) es) st
      (ExtArgsK is_static skip_check sig opts target
        (DROP (LENGTH (FST (SND sig))) es) k) ∧
  apply_vals cx kwargs st (ExtKwargsK is_static skip_check sig opts target results k) =
    liftk cx ApplyTv (do
      vs <- read_results cx results;
      eval_ext_call cx is_static skip_check sig opts (target ++ vs ++ kwargs)
    od st) k ∧
  apply_vals cx dflt_vs st (IntCallK1 all_tenv src_fn args results prev ret body nr mut k) =
    (case do
      set_scopes prev;
      vs <- read_results (cx with stk updated_by TL) results;
      env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs)) "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
      is_view <<- (mut = View ∨ mut = Pure);
      (* Acquire lock BEFORE push_function so scopes are unmodified on failure *)
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
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
      type_check (LENGTH vs = 3) "raw_call args";
      target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
      calldata <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
      amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
      eval_raw_call cx flags target_addr calldata amount
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (RawCallCalldataK flags k) =
    (case do
      type_check (LENGTH vs = 2) "raw_call calldata args";
      target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
      amount <- lift_option_type (dest_NumV (EL 1 vs)) "raw_call value";
      eval_raw_call cx flags target_addr cx.txn.calldata amount
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (RawLogK k) =
    (case do
      type_check (LENGTH vs = 2) "raw_log args";
      topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
      data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
      topic_vals <<- (case topics of
         TupleV tvs => tvs | DynArrayV tvs => tvs | _ => []);
      type_check (LENGTH topic_vals ≤ 4) "raw_log too many topics";
      push_log (encode_raw_event_values cx.txn.target topic_vals data);
      return $ Value NoneV
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (RawRevertK k) =
    (case do
      type_check (LENGTH vs = 1) "raw_revert args";
      raise $ Error $ RuntimeError "raw_revert"
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (SelfDestructK k) =
    (case do
      type_check (LENGTH vs = 1) "selfdestruct args";
      target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
      accounts <- get_accounts;
      self_acct <<- lookup_account cx.txn.target accounts;
      balance <<- self_acct.balance;
      transfer_value cx.txn.target target_addr balance;
      return $ Value NoneV
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx prefix st
      (BlueprintPrefixK arg_tys kind has_salt rof suffix k) =
    (case check_create_blueprint has_salt prefix st of
       (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL code_size, st) =>
         eval_expr_results_cps cx suffix st
           (ReadResultsK (BlueprintSuffixK prefix
             (CreateK arg_tys kind has_salt rof (SOME code_size) k)))) ∧
  apply_vals cx suffix st (BlueprintSuffixK prefix k) =
    AK cx (ApplyVals (prefix ++ suffix)) st k ∧
  apply_vals cx prefix st (RawCreatePrefixK arg_tys has_salt rof es k) =
    eval_expr_results_cps cx (TAKE (LENGTH es - (if has_salt then 1 else 0)) es) st
      (RawCreateArgsK prefix (DROP (LENGTH es - (if has_salt then 1 else 0)) es)
        (CreateK arg_tys RawCreate has_salt rof NONE k)) ∧
  apply_vals cx salt st (RawCreateSaltK prefix args k) =
    AK cx (ApplyVals (prefix ++ args ++ salt)) st k ∧
  apply_vals cx vs st (CreateK arg_tys kind has_salt rof blueprint_size k) =
    (case eval_create cx kind has_salt rof arg_tys vs blueprint_size st of
       (INR ex, st) => AK cx (ApplyExc ex) st k
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

val APPLY_VALS_PRE_CASE_TAC =
  simp[Once apply_vals_pre_def] >>
  gvs[check_def, type_check_def, assert_def] >>
  strip_tac >> gvs[];

Theorem apply_vals_pre[cv_pre]:
  ∀a b c d. apply_vals_pre a b c d
Proof
  ho_match_mp_tac apply_vals_ind \\ rw[] >>
  TRY APPLY_VALS_PRE_CASE_TAC >>
  gvs[check_create_blueprint_state, CaseEq"prod", CaseEq"sum"] >>
  TRY (Cases_on `vs` >> simp[]) >>
  rpt strip_tac >> gvs[optionTheory.IS_SOME_DEF]
QED

Definition nextk_def[simp]:
  nextk (AK _ _ _ k) = k
End

val () = cv_auto_trans nextk_def;

(* Captured arguments keep their locations until the caller stages values. *)
Definition apply_results_def:
  apply_results cx results st (ExprResultsK1 tv k) =
    apply_results cx (tv::results) st k ∧
  apply_results cx results st (ReadResultsK k) =
    liftk cx ApplyVals (read_results cx results st) k ∧
  apply_results cx results st
      (ExtArgsK is_static skip_check sig opts target kwargs k) =
    eval_exprs_cps cx kwargs st
      (ExtKwargsK is_static skip_check sig opts target results k) ∧
  apply_results cx results st (RawCreateArgsK prefix salt k) =
    (case read_results cx results st of
       (INR ex,st) => AK cx (ApplyExc ex) st k
     | (INL vs,st) => eval_exprs_cps cx salt st (RawCreateSaltK prefix vs k)) ∧
  apply_results cx results st (IntCallK all_tenv src_fn args dflts ret body nr mut k) =
    (case do
      prev <- get_scopes;
      set_scopes [FEMPTY];
      return prev
    od st of
     | (INR ex,st) => apply_exc cx ex st k
     | (INL prev,st) =>
        eval_exprs_cps (cx with stk updated_by CONS src_fn)
          (DROP (LENGTH dflts - (LENGTH args - LENGTH results)) dflts) st
          (IntCallK1 all_tenv src_fn args results prev ret body nr mut k)) ∧
  apply_results cx results st DoneK = AK cx (ApplyResults results) st DoneK ∧
  apply_results cx results st _ =
    AK cx (ApplyExc (Error (TypeError "apply_results k"))) st DoneK
End

val () = apply_results_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition stepk_def:
  stepk (AK cx ak st k) =
  case ak of
     | Apply => apply cx st k
     | ApplyExc ex => apply_exc cx ex st k
     | ApplyTv tv => apply_tv cx tv st k
     | ApplyVal v => apply_val cx v st k
     | ApplyVals vs => apply_vals cx vs st k
     | ApplyResults results => apply_results cx results st k
     | ApplyPlace p => apply_place cx p st k
End

val () = cv_auto_trans stepk_def;

Definition cont_def:
  cont ak = OWHILE (λak. nextk ak ≠ DoneK) stepk ak
End


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




Triviality apply_exc_owhile_eq:
  ∀cx ex st k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk (AK cx (ApplyExc ex) st k) =
  (if k ≠ DoneK then OWHILE (λak. nextk ak ≠ DoneK) stepk (apply_exc cx ex st k)
   else SOME (AK cx (ApplyExc ex) st DoneK))
Proof
  rw[Once OWHILE_THM, stepk_def]
QED

Triviality context_stk_pop_push[simp]:
  ∀cx src_fn. (cx with stk updated_by TL ∘ CONS src_fn) = cx
Proof
  rw[evaluation_context_component_equality, o_DEF, FUN_EQ_THM]
QED













Theorem cont_step[local]:
  !a. nextk a <> DoneK ==> cont a = cont (stepk a)
Proof
  rpt strip_tac >> simp[cont_def, Once OWHILE_THM]
QED

Theorem cont_apply_exc[local]:
  cont (apply_exc cx ex st k) = cont (AK cx (ApplyExc ex) st k)
Proof
  Cases_on `k = DoneK` >- gvs[apply_exc_def] >>
  qspec_then `AK cx (ApplyExc ex) st k` mp_tac cont_step >>
  simp[stepk_def]
QED

Theorem cont_conditionalk[local]:
  cont (liftk cx ApplyTv res (ConditionalK k)) =
  cont (case res of
      (INL tv,st1) => liftk cx ApplyTv (conditional_result cx tv st1) k
    | (INR ex,st1) => AK cx (ApplyExc ex) st1 k)
Proof
  Cases_on `res` >> Cases_on `q` >> simp[liftk1]
  >- (qspec_then `AK cx (ApplyTv x) r (ConditionalK k)` mp_tac cont_step >>
      simp[stepk_def, apply_tv_def, liftk1]) >>
  qspec_then `AK cx (ApplyExc y) r (ConditionalK k)` mp_tac cont_step >>
  simp[stepk_def, apply_exc_def]
QED

Theorem cont_ifk2_finally[local]:
  cont (liftk cx (K Apply) (m st) (IfK2 k)) =
  cont (liftk cx (K Apply) (finally m pop_scope st) k)
Proof
    Cases_on `m st` >> Cases_on `q` >>
  gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def,
      liftk1, cont_def, Once OWHILE_THM, stepk_def,
      apply_def, apply_exc_def] >>
  Cases_on `pop_scope r` >> Cases_on `q` >> gvs[]
QED

Theorem eval_cps_mutual:
 (∀cx s st k. cont (eval_stmt_cps cx s st k) =
   cont (liftk cx (K Apply) (eval_stmt cx s st) k)) /\
 (∀cx ss st k. cont (eval_stmts_cps cx ss st k) =
   cont (liftk cx (K Apply) (eval_stmts cx ss st) k)) /\
 (∀cx it st k. cont (eval_iterator_cps cx it st k) =
   cont (liftk cx ApplyVals (eval_iterator cx it st) k)) /\
 (∀cx tyv nm body vs st k. cont (eval_for_cps cx tyv nm body vs st k) =
   cont (liftk cx (K Apply) (eval_for cx tyv nm body vs st) k)) /\
 (∀cx e st k. cont (eval_expr_cps cx e st k) =
   cont (liftk cx ApplyTv (eval_expr cx e st) k)) /\
 (∀cx es st k. cont (eval_exprs_cps cx es st k) =
   cont (liftk cx ApplyVals (eval_exprs cx es st) k)) /\
 (∀cx t st k. cont (eval_base_place_cps cx t st k) =
   cont (liftk cx ApplyTv (eval_base_place cx t st) k)) /\
 (∀cx t st k. cont (eval_target_place_cps cx t st k) =
   cont (liftk cx ApplyPlace (eval_target_place cx t st) k)) /\
 (∀cx g v st k. cont (assign_tuple_targets_cps cx g v st k) =
   cont (liftk cx (K Apply) (assign_tuple_targets cx g v st) k)) /\
 (∀cx gs vs st k. cont (assign_tuple_target_list_cps cx gs vs st k) =
   cont (liftk cx (K Apply) (assign_tuple_target_list cx gs vs st) k)) /\
 (∀cx es st k. cont (eval_expr_results_cps cx es st k) =
   cont (liftk cx ApplyResults (eval_expr_results cx es st) k))
Proof
  ho_match_mp_tac evaluate_ind
  >> pure_rewrite_tac [liftk1]
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
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[Once OWHILE_THM, stepk_def]
    \\ rename1 `INL v` \\ Cases_on`v`
    \\ simp[dest_StringV_def, lift_option_def, lift_option_type_def, return_def,
            raise_def, apply_val_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM] )
  \\ conj_tac >- ( (* Raise (RaiseCustomError err) *)
    Cases_on `err`
    \\ rw[eval_stmt_cps_def, evaluate_def]
    \\ CASE_TAC
    >- rw[raise_def, cont_def]
    \\ CASE_TAC
    >- rw[raise_def, cont_def]
    \\ CASE_TAC
    >- rw[raise_def, cont_def]
    \\ rw[bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def]
    \\ CASE_TAC
    \\ gvs[lift_option_def, lift_option_type_def, return_def, raise_def,
           apply_exc_owhile_eq, apply_exc_def, stepk_def]
    \\ Cases_on `k = DoneK`
    \\ gvs[apply_exc_def]
    \\ rw[Once OWHILE_THM] )
  \\ conj_tac >- ( (* Assert e AssertBare *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ simp[switch_BoolV_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rename1 `INL v`
    \\ rw[return_def, raise_def]
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
    \\ simp[switch_BoolV_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rename1 `INL v`
    \\ rw[return_def, raise_def]
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
    \\ simp[switch_BoolV_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rename1 `INL v`
    \\ rw[return_def, raise_def]
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
      \\ CASE_TAC \\ reverse CASE_TAC
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def]
      \\ rename1 `INL sv`
      \\ Cases_on`sv`
      \\ simp[dest_StringV_def, lift_option_def, lift_option_type_def,
              return_def, raise_def, apply_val_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
    \\ Cases_on`v` \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Assert e (AssertCustomError err) *)
    Cases_on `err`
    \\ rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ simp[switch_BoolV_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rename1 `INL v`
    \\ rw[return_def, raise_def]
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_def] )
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ CASE_TAC
      >- (gvs[raise_def] \\
          gvs[apply_exc_owhile_eq, apply_exc_def, stepk_def] \\
          Cases_on `k = DoneK` \\ gvs[apply_exc_def] \\
          rw[Once OWHILE_THM])
      \\ CASE_TAC
      >- (gvs[raise_def] \\
          gvs[apply_exc_owhile_eq, apply_exc_def, stepk_def] \\
          Cases_on `k = DoneK` \\ gvs[apply_exc_def] \\
          rw[Once OWHILE_THM])
      \\ CASE_TAC
      >- (gvs[raise_def] \\
          gvs[apply_exc_owhile_eq, apply_exc_def, stepk_def] \\
          Cases_on `k = DoneK` \\ gvs[apply_exc_def] \\
          rw[Once OWHILE_THM])
      \\ first_x_assum drule \\ rw[cont_def]
      \\ rw[bind_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def]
      \\ CASE_TAC
      \\ gvs[lift_option_def, lift_option_type_def, return_def, raise_def,
             apply_exc_owhile_eq, apply_exc_def, stepk_def]
      \\ Cases_on `k = DoneK`
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM] )
    \\ Cases_on`v` \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Log id es *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1])
  \\ conj_tac >- ( (* AnnAssign id typ e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    \\ gvs[lift_option_type_def, raise_def, return_def, cont_def]
    \\ Cases_on `eval_expr cx e st` \\ Cases_on `q` \\ gvs[]
    >- (rename1 `eval_expr cx e st = (INL tv,st1)`
        \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
        \\ Cases_on `read_result cx tv st1` \\ Cases_on `q` \\ gvs[]
        >- rw[Once OWHILE_THM, stepk_def, liftk1, apply_val_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
  \\ conj_tac >- ( (* Append t e *)
    rpt gen_tac >> strip_tac
    >> pure_once_rewrite_tac [eval_stmt_cps_def, evaluate_def]
    >> rw[bind_def]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_place_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1] )
  \\ conj_tac >- suspend "AssignPlace"
  \\ conj_tac >- suspend "AssignTuple"
  \\ conj_tac >- suspend "AugAssign"
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
    \\ pure_rewrite_tac [GSYM (SRULE [cont_def, liftk1] cont_ifk2_finally)]
    \\ Cases_on `read_result cx x r''` \\ Cases_on `q`
    \\ gvs[bind_def, raise_def, liftk1]
    >- (
      Cases_on `x'` \\ gvs[raise_def]
      \\ Cases_on `b` \\ gvs[]
      \\ first_x_assum irule \\ goal_assum drule ) )
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
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_array_def,
          liftk1, lift_option_type_def]
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
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_range2_def, liftk1]
    \\ gvs[]
    \\ first_x_assum $ drule_then drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_range2_def, liftk1]
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
    \\ Cases_on `read_result cx x r` \\ Cases_on `q`
    \\ gvs[bind_def, raise_def]
    >- (
      Cases_on `x'` \\ gvs[raise_def]
      \\ simp[Once OWHILE_THM, SimpLHS, stepk_def, apply_val_def]
      \\ pure_rewrite_tac[GSYM cont_def]
      \\ simp[cont_apply_exc]
      \\ Cases_on `b` \\ gvs[]
      \\ fs[GSYM cont_def, GSYM liftk1]
      \\ simp[cont_conditionalk]
      \\ rename1 `eval_expr cx branch r''`
      \\ Cases_on `eval_expr cx branch r''`
      \\ Cases_on `q` \\ simp[liftk1])
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
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
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_subscript_def, liftk1, bind_def])
  \\ conj_tac >- ( (* eval_expr (Attribute e id) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1] )
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
    rpt gen_tac >> strip_tac
    >> pure_once_rewrite_tac [eval_expr_cps_def, evaluate_def]
    >> rw[bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_place_def, bind_def, liftk1] )
  \\ conj_tac >- ( (* eval_expr (TypeBuiltin ...) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1] )
  \\ conj_tac >- ( (* eval_expr (Call (Send has_gas) es _) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1]
    >> gvs[apply_exc_def] )
  \\ conj_tac >- ( (* eval_expr (Call (ExtCall ...) es _) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def]
    \\ first_x_assum drule_all
    \\ simp[] \\ disch_then kall_tac
    \\ CASE_TAC \\ reverse CASE_TAC \\ gvs[]
    >- simp[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_results_def]
    \\ first_x_assum drule_all
    \\ simp[rich_listTheory.DROP_DROP_T] \\ disch_then kall_tac
    \\ CASE_TAC \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def, apply_vals_def,
          bind_def, liftk1]
    \\ simp[prod_CASE_rator, sum_CASE_rator])
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
    >> pop_assum mp_tac
    >> simp[CaseEq"prod",CaseEq"sum",return_def]
    >> strip_tac >> gvs[]
    >> first_x_assum drule_all
    >> simp[cont_def]
    >> disch_then kall_tac
    >> CASE_TAC
    \\ reverse CASE_TAC
    >- gvs[return_def, raise_def, apply_exc_owhile_eq,
           Once OWHILE_THM, stepk_def, apply_exc_def]
    >> simp[Once OWHILE_THM, stepk_def, apply_results_def, bind_def]
    >> CASE_TAC
    >> reverse CASE_TAC
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> simp[ignore_bind_def, bind_def]
    >> CASE_TAC
    >> reverse CASE_TAC
    >- gvs[set_scopes_def,return_def]
    >> pop_assum mp_tac
    >> simp[return_def]
    >> strip_tac
    >> first_x_assum drule_all
    >> drule eval_expr_results_length >> strip_tac
    >> simp[cont_def]
    >> disch_then kall_tac
    \\ CASE_TAC
    \\ reverse CASE_TAC
    >- gvs[return_def, raise_def, apply_exc_owhile_eq,
           Once OWHILE_THM, stepk_def, apply_exc_def, o_DEF,
           finally_def, bind_def, ignore_bind_def, liftk1,
           set_scopes_def, return_def]
    >> qmatch_goalsub_abbrev_tac`finally mm ss zz`
    >> Cases_on`finally mm ss zz`
    >> simp[]
    >> reverse $ Cases_on`q`
    >> simp[Abbr`ss`,Abbr`zz`]
    >- (
      pop_assum mp_tac >>
      simp[finally_def, ignore_bind_def, bind_def, return_def, raise_def] >>
      simp[CaseEq"prod",CaseEq"sum"] >>
      simp[set_scopes_def, return_def] >>
      simp[Abbr`mm`, bind_def])
    >> qunabbrev_tac`mm`
    >> simp[Once OWHILE_THM,stepk_def,apply_vals_def,bind_def,ignore_bind_def]
    >> simp[Once set_scopes_def, return_def]
    >> qhdtm_x_assum`finally` (fn th => mk_asm "defaults" th >> mp_tac th)
    >> simp[finally_def,bind_def,ignore_bind_def]
    >> simp[Once set_scopes_def, return_def]
    >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `?q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> asm_x "defaults" assume_tac
    >> qmatch_asmsub_rename_tac `(if _ then _ else _) _ = (INL lock_result,_)`
    >> Cases_on `lock_result`
    >> first_x_assum drule_all
    >> simp[cont_def] >> disch_then kall_tac
    >> simp[try_def, bind_def]
    >> CASE_TAC
    >> reverse CASE_TAC
    >> simp[]
    >- (
      simp[Once OWHILE_THM, stepk_def] >>
      simp[apply_exc_def, liftk1, finally_def, bind_def] >>
      qmatch_goalsub_rename_tac`handle_function ff ss` >>
      Cases_on`handle_function ff ss` >>
      simp[return_def, ignore_bind_def, bind_def] >>
      AP_TERM_TAC >>
      gvs[push_function_def, return_def] >>
      (* chains are pure computation; dead assumptions only slow simp down *)
      POP_ASSUM_LIST (K ALL_TAC) >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[return_def, raise_def] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] )
    >> simp[Once OWHILE_THM, stepk_def, apply_def, liftk1]
    >> simp[bind_def, return_def, ignore_bind_def]
    >> gvs[push_function_def, return_def]
    >> AP_TERM_TAC >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[return_def, raise_def] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      ALL_TAC >| [CASE_TAC, CASE_TAC, CASE_TAC, CASE_TAC, CASE_TAC] >> simp[] >>
      ALL_TAC >| [CASE_TAC, CASE_TAC, CASE_TAC, CASE_TAC, CASE_TAC, CASE_TAC] >> simp[] >>
      CASE_TAC >> simp[])
  (* ===== Chain interaction builtins ===== *)
  (* All 5 new cases: CPS eval_exprs then continuation matches big-step body.
     Pattern: unfold both sides, use IH for eval_exprs, match continuation bodies. *)
  (* Chain interaction builtins: all use same tactic.
     CPS evals exprs then calls apply_vals which matches big-step body.
      Applied per-case (not via rpt) to stay within the per-tactic budget. *)
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    Cases_on `kind`
    >- (
      rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
      \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
      \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
            apply_exc_def, apply_vals_def, ignore_bind_def, bind_def]
      \\ gvs[check_create_blueprint_state, CaseEq"prod", CaseEq"sum"]
      \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
      \\ qpat_x_assum `∀a b c d e f. _` drule_all
      \\ strip_tac \\ gvs[]
      \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
            apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
    >- (
      rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
      \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
      \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
            apply_exc_def, apply_vals_def])
    >- (
      rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
      \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
      \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
            apply_exc_def, apply_vals_def]
      \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
      \\ qpat_x_assum `∀a b c d e f. _` drule_all
      \\ strip_tac \\ gvs[]
      \\ CASE_TAC \\ gvs[]
      \\ (reverse CASE_TAC >- (
        gvs[]
        \\ rw[Once OWHILE_THM, nextk_def, stepk_def, apply_exc_def]
        \\ rw[Once OWHILE_THM, nextk_def, stepk_def, apply_exc_def]
        \\ rw[Once OWHILE_THM, nextk_def, stepk_def, apply_exc_def]))
      \\ gvs[]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
            apply_results_def, liftk1]
      \\ gvs[prod_CASE_rator, sum_CASE_rator]
      \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
            apply_exc_def, apply_vals_def]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
            apply_exc_def, apply_vals_def])
    \\ rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def]
    \\ qpat_x_assum `∀a b c. _` drule_all
    \\ strip_tac \\ gvs[]
    \\ CASE_TAC \\ gvs[]
    \\ (reverse CASE_TAC >- (
      gvs[] \\ rw[Once OWHILE_THM, nextk_def, stepk_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, nextk_def, stepk_def, apply_exc_def]))
    \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def, apply_results_def]
    \\ CASE_TAC \\ gvs[]
    \\ (reverse CASE_TAC >- (
      gvs[] \\ rw[Once OWHILE_THM, nextk_def, stepk_def, apply_exc_def]))
    \\ gvs[]
    \\ qpat_x_assum `∀a b c d e f g h i. _` drule_all
    \\ strip_tac \\ gvs[]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def])
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def] (* eval_exprs [] *)
  \\ conj_tac >- ( (* eval_exprs (e::es) *)
  rw[eval_expr_cps_def, evaluate_def, bind_def]
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
  \\ rw[Once OWHILE_THM, stepk_def])
  >> suspend "Places"
QED

Resume eval_cps_mutual[AssignPlace]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [eval_stmt_cps_def, evaluate_def]
  >> rw[bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_tv_def]
  >> gvs[cont_def]
  >> first_x_assum drule >> rw[]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_place_def, liftk1, bind_def]
QED

Resume eval_cps_mutual[AssignTuple]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [eval_stmt_cps_def, evaluate_def]
  >> rw[bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_val_def]
  >> gvs[cont_def]
  >> first_x_assum irule >> metis_tac[]
QED

Resume eval_cps_mutual[AugAssign]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [eval_stmt_cps_def, evaluate_def]
  >> rw[bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_place_def, bind_def, return_def]
  >> CASE_TAC
  >> qmatch_asmsub_rename_tac `read_place cx p sr = (qr,tr)`
  >> Cases_on `qr` >> gvs[]
  >> CASE_TAC
  >> qmatch_asmsub_rename_tac `place_type_value cx p tr = (qt,tt)`
  >> Cases_on `qt` >> gvs[]
  >> gvs[cont_def]
  >> first_x_assum (drule_all_then assume_tac)
  >> rw[]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1, bind_def]
QED
Resume eval_cps_mutual[Places]:
  conj_tac >- rw[eval_base_place_cps_def, evaluate_def, liftk1]
  >> conj_tac >- rw[eval_base_place_cps_def, evaluate_def, liftk1]
  >> conj_tac >- suspend "BasePlaceAttribute"
  >> conj_tac >- suspend "BasePlaceSubscript"
  >> conj_tac >- suspend "TargetPlace"
  >> conj_tac >- suspend "TupleStore"
  >> conj_tac >- suspend "TupleStores"
  >> conj_tac >- rw[assign_tuple_targets_cps_def, evaluate_def, return_def]
  >> conj_tac >- suspend "TupleStoresCons"
  >> conj_tac >- rw[assign_tuple_targets_cps_def, evaluate_def, raise_def]
  >> conj_tac >- rw[assign_tuple_targets_cps_def, evaluate_def, raise_def]
  >> conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def]
  >> suspend "ExprResultsCons"
QED

Resume eval_cps_mutual[ExprResultsCons]:
  rw[eval_expr_cps_def, evaluate_def, bind_def]
  >> CASE_TAC >> gvs[cont_def] >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_tv_def]
  >> qpat_x_assum `∀a b c. _` drule_all >> rw[]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[return_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_results_def]
  >> rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_results_def]
  >> gvs[apply_results_def]
  >> rw[Once OWHILE_THM, stepk_def]
QED

Resume eval_cps_mutual[BasePlaceAttribute]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [eval_base_place_cps_def, evaluate_def]
  >> rw[bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
QED
Resume eval_cps_mutual[BasePlaceSubscript]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [eval_base_place_cps_def, evaluate_def]
  >> rw[bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_tv_def]
  >> gvs[cont_def]
  >> first_x_assum drule >> rw[]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1, bind_def]
QED
Resume eval_cps_mutual[TargetPlace]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [eval_target_place_cps_def, evaluate_def]
  >> rw[bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
QED
Resume eval_cps_mutual[TupleStore]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [assign_tuple_targets_cps_def, evaluate_def]
  >> rw[bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_place_def, liftk1]
QED
Resume eval_cps_mutual[TupleStores]:
  rpt gen_tac >> strip_tac
  >> Cases_on `v` >> simp[assign_tuple_targets_cps_def, Once evaluate_def, raise_def]
  >> rename1 `ArrayV a` >> Cases_on `a`
  >> gvs[assign_tuple_targets_cps_def, Once evaluate_def, raise_def]
QED
Resume eval_cps_mutual[TupleStoresCons]:
  rpt gen_tac >> strip_tac
  >> pure_once_rewrite_tac [assign_tuple_targets_cps_def, evaluate_def]
  >> rw[bind_def, ignore_bind_def]
  >> CASE_TAC >> reverse CASE_TAC
  >- rw[cont_def, Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[cont_def, Once OWHILE_THM, stepk_def, apply_def]
  >> gvs[cont_def]
  >> first_x_assum drule >> rw[]
QED
Finalise eval_cps_mutual

Theorem eval_cps_eq:
  (!cx s st k. cont (eval_stmt_cps cx s st k) =
    cont ((case eval_stmt cx s st of (INL (),st1) => AK cx Apply st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) /\
  (!cx ss st k. cont (eval_stmts_cps cx ss st k) =
    cont ((case eval_stmts cx ss st of (INL (),st1) => AK cx Apply st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) /\
  (!cx it st k. cont (eval_iterator_cps cx it st k) =
    cont ((case eval_iterator cx it st of (INL vs,st1) => AK cx (ApplyVals vs) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) /\
  (!cx tyv nm body vs st k. cont (eval_for_cps cx tyv nm body vs st k) =
    cont ((case eval_for cx tyv nm body vs st of (INL (),st1) => AK cx Apply st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) /\
  (!cx e st k. cont (eval_expr_cps cx e st k) =
    cont ((case eval_expr cx e st of (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k)) /\
  (!cx es st k. cont (eval_exprs_cps cx es st k) =
    cont ((case eval_exprs cx es st of (INL vs,st1) => AK cx (ApplyVals vs) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k))
Proof
  simp[eval_cps_mutual, GSYM liftk1, combinTheory.K_DEF]
QED

Definition fromk_def[simp]:
  fromk x =
    case x of
      (SOME (AK cx Apply st DoneK)) => (INL (), st)
    | (SOME (AK cx (ApplyExc ex) st DoneK)) => (INR ex, st)
    | _ => (INR $ Error (TypeError "fromk"), empty_state)
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
  fromtvk x =
    case x of
      (SOME (AK cx (ApplyTv tv) st DoneK)) => (INL tv, st)
    | (SOME (AK cx (ApplyExc ex) st DoneK)) => (INR ex, st)
    | _ => (INR $ Error (TypeError "fromtvk"), empty_state)
End

val () = cv_auto_trans fromtvk_def;

Theorem eval_expr_eq_cont_cps:
  eval_expr cx e st = fromtvk $ cont (eval_expr_cps cx e st DoneK)
Proof
  Cases_on`eval_expr cx e st`
  \\ qmatch_goalsub_rename_tac`res,st1`
  \\ qspecl_then[`cx`,`e`,`st`,`DoneK`]mp_tac(cj 5 eval_cps_eq)
  \\ simp[cont_def] \\ strip_tac
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC
  \\ Cases_on `res` \\ gvs[]
  \\ simp[fromtvk_def]
QED

val constants_env_pre_def = constants_env_def
  |> SRULE [bind_def, eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "constants_env_pre";

Theorem constants_env_pre[cv_pre]:
  ∀v0 v1 v2 v3 v acc. constants_env_pre v0 v1 v2 v3 v acc
Proof
  ho_match_mp_tac constants_env_ind
  \\ rw[]
  \\ rw[Once constants_env_pre_def]
  \\ gs[bind_def, eval_expr_eq_cont_cps]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_rename_tac`eval_expr_cps ec ee es DoneK`
  \\ qspecl_then[`ec`,`ee`,`es`,`DoneK`]mp_tac $ cj 5 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC
  \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM]
QED

val evaluate_defaults_pre_def = evaluate_defaults_def
  |> SRULE [bind_def, eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "evaluate_defaults_pre";

Theorem evaluate_defaults_pre[cv_pre]:
  ∀cx am v. evaluate_defaults_pre cx am v
Proof
  ntac 2 gen_tac
  \\ Induct \\ rw[]
  \\ rw[Once evaluate_defaults_pre_def]
  \\ gs[bind_def, eval_expr_eq_cont_cps]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_rename_tac`eval_expr_cps ec ee es DoneK`
  \\ qspecl_then[`ec`,`ee`,`es`,`DoneK`]mp_tac $ cj 5 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC
  \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM]
QED

val () = cv_auto_trans evaluate_all_constants_def;

val call_external_function_pre_def = call_external_function_def
     |> SRULE [eval_stmts_eq_cont_cps,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, COND_RATOR, option_CASE_rator,
               get_transient_storage_def, update_transient_def]
     |> cv_auto_trans_pre "call_external_function_pre";

Theorem call_external_function_pre[cv_pre]:
  call_external_function_pre orc am cx nr mut ts all_mods args dflts vals
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
val () = cv_auto_trans clear_machine_logs_def;
val () = cv_auto_trans call_external_transaction_def;

val () = cv_auto_trans load_contract_def;

(* CV validity only: expression evaluation reaches DoneK.  Registering this
   precondition does not replace the CPS computation by its big-step result.
   Keep it after existing translations so their equations are unchanged. *)
Theorem cont_pre_eval_expr_cps[cv_pre]:
  cont_pre (eval_expr_cps cx e st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont]
  \\ qspecl_then[`cx`,`e`,`st`,`DoneK`]mp_tac $ cj 5 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM]
QED
Theorem cont_pre_eval_stmts_cps[cv_pre]:
  cont_pre (eval_stmts_cps cx ss st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont]
  \\ qspecl_then[`cx`,`ss`,`st`,`DoneK`]mp_tac $ cj 2 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM]
QED


(* Integration audit: required CPS equivalences must be kernel closed. *)
val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("CPS oracle debt: " ^ name)
  end) (DB.thms "vyperSmallStep");
