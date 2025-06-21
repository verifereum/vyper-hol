open HolKernel boolLib bossLib Parse
     cv_transLib whileTheory pairTheory combinTheory
     listTheory arithmeticTheory vyperInterpreterTheory

val () = new_theory "vyperSmallStep";

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
  | AssertK expr eval_continuation
  | AssertK1 string eval_continuation
  | RaiseK eval_continuation
  | LogK identifier eval_continuation
  | PopK eval_continuation
  | AppendK expr eval_continuation
  | AppendK1 base_target_value eval_continuation
  | AnnAssignK identifier eval_continuation
  | AssignK expr eval_continuation
  | AssignK1 assignment_value eval_continuation
  | AugAssignK binop expr eval_continuation
  | AugAssignK1 base_target_value binop eval_continuation
  | IfK (stmt list) (stmt list) eval_continuation
  | IfK1 toplevel_value (stmt list) (stmt list) eval_continuation
  | IfK2 eval_continuation
  | ForK identifier num (stmt list) eval_continuation
  | ForK1 num (stmt list) (value list) eval_continuation
  | ExprK eval_continuation
  | StmtsK (stmt list) eval_continuation
  | ArrayK eval_continuation
  | RangeK1 expr eval_continuation
  | RangeK2 num eval_continuation
  | BaseTargetK eval_continuation
  | TupleTargetK eval_continuation
  | TargetsK (assignment_target list) eval_continuation
  | TargetsK1 assignment_value eval_continuation
  | AttributeTargetK identifier eval_continuation
  | SubscriptTargetK expr eval_continuation
  | SubscriptTargetK1 base_target_value eval_continuation
  | IfExpK expr expr eval_continuation
  | ArrayLitK bound eval_continuation
  | StructLitK (identifier list) eval_continuation
  | SubscriptK expr eval_continuation
  | SubscriptK1 toplevel_value eval_continuation
  | AttributeK identifier eval_continuation
  | BuiltinK builtin eval_continuation
  | CallSendK eval_continuation
  | IntCallK identifier ((identifier # type) list) (stmt list) eval_continuation
  | IntCallK1 (scope list) eval_continuation
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
  no_recursion (fn:identifier) stk ⇔ ¬MEM fn stk
End

val () = cv_auto_trans no_recursion_def;

val option_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="option",Tyop="option"}));

val sum_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="sum",Tyop="sum"}));

val prod_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="pair",Tyop="prod"}));

val toplevel_value_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperInterpreter",Tyop="toplevel_value"}));

Definition eval_base_target_cps_def:
  eval_base_target_cps cx (NameTarget id) st k =
    (let r = do
        sc <- get_scopes;
        n <<- string_to_num id;
        cs <- lift_option (find_containing_scope n sc) "NameTarget lookup";
        return $ (ScopedVar cs id, []) od st in
     liftk cx ApplyBaseTarget r k) ∧
  eval_base_target_cps cx (TopLevelNameTarget id) st k =
    AK cx (ApplyBaseTarget (TopLevelVar id, [])) st k ∧
  eval_base_target_cps cx (AttributeTarget t id) st k =
    eval_base_target_cps cx t st (AttributeTargetK id k) ∧
  eval_base_target_cps cx (SubscriptTarget t e) st k =
    eval_base_target_cps cx t st (SubscriptTargetK e k)
End

val () = eval_base_target_cps_def
  |> SRULE [bind_def, ignore_bind_def,
            LET_RATOR, lift_option_def,
            prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, liftk1]
  |> cv_auto_trans;

Definition eval_expr_cps_def:
  eval_expr_cps cx1 (Name id) st k =
    liftk cx1 ApplyTv
      (do env <- get_scopes;
          v <- lift_option (lookup_scopes (string_to_num id) env) "lookup Name";
          return $ Value v od st) k ∧
  eval_expr_cps cx2 (TopLevelName id) st k =
    liftk cx2 ApplyTv (lookup_global cx2 (string_to_num id) st) k ∧
  eval_expr_cps cx2 (FlagMember fid mid) st k =
    liftk cx2 ApplyTv (lookup_flag_mem cx2 fid mid st) k ∧
  eval_expr_cps cx3 (IfExp e1 e2 e3) st k =
    eval_expr_cps cx3 e1 st (IfExpK e2 e3 k) ∧
  eval_expr_cps cx4 (Literal l) st k =
    AK cx4 (ApplyTv (Value $ evaluate_literal l)) st k ∧
  eval_expr_cps cx5 (ArrayLit b es) st k =
    (case check (compatible_bound b (LENGTH es)) "ArrayLit bound" st of
       (INR ex, st) => AK cx5 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx5 es st (ArrayLitK b k)) ∧
  eval_expr_cps cx5 (StructLit id kes) st k =
    eval_exprs_cps cx5 (MAP SND kes) st (StructLitK (MAP FST kes) k) ∧
  eval_expr_cps cx6 (Subscript e1 e2) st k =
    eval_expr_cps cx6 e1 st (SubscriptK e2 k) ∧
  eval_expr_cps cx7 (Attribute e id) st k =
    eval_expr_cps cx7 e st (AttributeK id k) ∧
  eval_expr_cps cx8 (Builtin bt es) st k =
    (case check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st of
       (INR ex, st) => AK cx8 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx8 es st (BuiltinK bt k)) ∧
  eval_expr_cps cx8 (Pop bt) st k =
    eval_base_target_cps cx8 bt st (PopK k) ∧
  eval_expr_cps cx8 (TypeBuiltin Empty typ) st k =
    (case do
       ts <- lift_option (get_self_code cx8) "Empty get_self_code";
       return $ Value $ default_value (type_env ts) typ od st
     of (INR ex, st) => AK cx8 (ApplyExc ex) st k
      | (INL tv, st) => AK cx8 (ApplyTv tv) st k) ∧
  eval_expr_cps cx8 (TypeBuiltin MaxValue typ) st k =
    liftk cx8 ApplyTv (do
      v <- lift_sum $ evaluate_max_value typ;
      return $ Value v
    od st) k ∧
  eval_expr_cps cx8 (TypeBuiltin _ typ) st k =
    AK cx8 (ApplyExc (Error "TODO: TypeBuiltin")) st k ∧
  eval_expr_cps cx9 (Call Send es) st k =
    (case check (LENGTH es = 2) "Send args" st of
       (INR ex, st) => AK cx9 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx9 es st (CallSendK k)) ∧
  eval_expr_cps cx10 (Call (ExtCall _) _) st k =
    AK cx10 (ApplyExc (Error "TODO: ExtCall")) st k ∧
  eval_expr_cps cx10 (Call (IntCall fn) es) st k =
    (case do
      check (no_recursion fn cx10.stk) "recursion";
      ts <- lift_option (get_self_code cx10) "IntCall get_self_code";
      tup <- lift_option (lookup_function fn Internal ts) "IntCall lookup_function";
      args <<- FST tup; body <<- SND $ SND tup;
      check (LENGTH args = LENGTH es) "IntCall args length";
      return (args, body) od st
     of (INR ex, st) => AK cx10 (ApplyExc ex) st k
      | (INL (args, body), st) =>
          eval_exprs_cps cx10 es st (IntCallK fn args body k)) ∧
  eval_exprs_cps cx11 [] st k = AK cx11 (ApplyVals []) st k ∧
  eval_exprs_cps cx12 (e::es) st k =
    eval_expr_cps cx12 e st (ExprsK es k)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (cx,e,st,k) => expr_size e
    | INR (cx,es,st,k) => list_size expr_size es)’
  \\ rw[expr1_size_map, SUM_MAP_expr2_size, list_size_SUM_MAP, MAP_MAP_o,
        list_size_pair_size_map]
End

val eval_expr_cps_pre_def = eval_expr_cps_def
   |> SRULE
        [liftk1, bind_def, ignore_bind_def,
         LET_RATOR, option_CASE_rator,
         sum_CASE_rator, prod_CASE_rator, lift_option_def]
   |> cv_auto_trans_pre;

Theorem eval_expr_cps_pre[cv_pre]:
  (∀a b c d. eval_expr_cps_pre a b c d) ∧
  (∀x y z w. eval_exprs_cps_pre x y z w)
Proof
  ho_match_mp_tac eval_expr_cps_ind \\ rw[]
  \\ rw[Once eval_expr_cps_pre_def]
  \\ gvs[CaseEq"prod", CaseEq"sum", CaseEq"option", raise_def, check_def]
  \\ first_x_assum irule
  \\ gvs[bind_def, ignore_bind_def, lift_option_def]
QED

Definition eval_iterator_cps_def:
  eval_iterator_cps cx (Array e) st k =
    eval_expr_cps cx e st (ArrayK k) ∧
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
  eval_stmt_cps cx (Raise se) st k = eval_expr_cps cx se st (RaiseK k) ∧
  eval_stmt_cps cx (Assert e se) st k = eval_expr_cps cx se st (AssertK e k) ∧
  eval_stmt_cps cx (Log id es) st k = eval_exprs_cps cx es st (LogK id k) ∧
  eval_stmt_cps cx (AnnAssign id typ e) st k =
    eval_expr_cps cx e st (AnnAssignK id k) ∧
  eval_stmt_cps cx (Append t e) st k =
    eval_base_target_cps cx t st (AppendK e k) ∧
  eval_stmt_cps cx (Assign g e) st k =
    eval_target_cps cx g st (AssignK e k) ∧
  eval_stmt_cps cx (AugAssign t bop e) st k =
    eval_base_target_cps cx t st (AugAssignK bop e k) ∧
  eval_stmt_cps cx (If e ss1 ss2) st k =
    eval_expr_cps cx e st (IfK ss1 ss2 k) ∧
  eval_stmt_cps cx (For id typ it n body) st k =
    eval_iterator_cps cx it st (ForK id n body k) ∧
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
  eval_for_cps cx nm body [] st k = AK cx Apply st k ∧
  eval_for_cps cx nm body (v::vs) st k =
  (case push_scope_with_var nm v st of
        (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_stmts_cps cx body st (ForK1 nm body vs k))
End

val () = cv_auto_trans eval_for_cps_def;

Definition apply_def:
  apply cx st (StmtsK ss k) =
    eval_stmts_cps cx ss st k ∧
  apply cx st (ForK1 nm body vs k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_for_cps cx nm body vs st k) ∧
  apply cx st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx Apply st k) ∧
  apply cx st (IfK1 (Value (BoolV b)) ss1 ss2 k) =
    eval_stmts_cps cx (if b then ss1 else ss2) st (IfK2 k) ∧
  apply cx st (IfK1 (Value _) ss1 ss2 k) =
    AK cx (ApplyExc $ Error "not BoolV") st (IfK2 k) ∧
  apply cx st (IfK1 _ ss1 ss2 k) =
    AK cx (ApplyExc $ Error "not Value") st (IfK2 k) ∧
  apply cx st (IntCallK1 prev k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (do pop_function prev; return NoneV od st) k ∧
  apply cx st DoneK = AK cx Apply st DoneK ∧
  apply cx st _ = AK cx (ApplyExc $ Error "apply k") st DoneK
End

val () = apply_def
  |> SRULE [liftk1, ignore_bind_def, bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_exc_def:
  apply_exc cx ex st (ReturnK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssertK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssertK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RaiseK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (LogK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AnnAssignK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssignK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssignK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK1 _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK1 _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx (ApplyExc ex) st k) ∧
  apply_exc cx ex st (ForK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ForK1 nm body vs k) =
    (case finally (handle_loop_exception ex) pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL broke, st) =>
          if broke then AK cx Apply st k
          else eval_for_cps cx nm body vs st k) ∧
  apply_exc cx ex st (ExprK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StmtsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ArrayK k) = AK cx (ApplyExc ex) st k ∧
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
  apply_exc cx ex st (ArrayLitK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StructLitK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (PopK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BuiltinK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CallSendK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK1 prev k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (finally (handle_function ex) (pop_function prev) st)
      k ∧
  apply_exc cx ex st (ExprsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExprsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st DoneK = AK cx (ApplyExc ex) st DoneK
End

val () = apply_exc_def
  |> SRULE [finally_def, bind_def, ignore_bind_def,
            liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_targets_def:
  apply_targets cx gvs st (TargetsK1 gv k) =
    AK cx (ApplyTargets (gv::gvs)) st k ∧
  apply_targets cx gvs st (TupleTargetK k) =
      AK cx (ApplyTarget (TupleTargetV gvs)) st k ∧
  apply_targets cx _ st _ =
    AK cx (ApplyExc $ Error "apply_targets k") st DoneK
End

val () = cv_auto_trans apply_targets_def;

Definition apply_base_target_def:
  apply_base_target cx btv st (BaseTargetK k) =
    AK cx (ApplyTarget (BaseTargetV (FST btv) (SND btv))) st k ∧
  apply_base_target cx btv st (AttributeTargetK id k) =
    AK cx (ApplyBaseTarget (FST btv, AttrSubscript id :: SND btv)) st k ∧
  apply_base_target cx btv st (SubscriptTargetK e k) =
    eval_expr_cps cx e st (SubscriptTargetK1 btv k) ∧
  apply_base_target cx btv st (AugAssignK bop e k) =
    eval_expr_cps cx e st (AugAssignK1 btv bop k) ∧
  apply_base_target cx btv st (AppendK e k) =
    eval_expr_cps cx e st (AppendK1 btv k) ∧
  apply_base_target cx btv st (PopK k) =
    liftk cx ApplyTv (do
      tv <- assign_target cx (BaseTargetV (FST btv) (SND btv)) PopOp;
      v <- get_Value tv;
      vs <- lift_option (extract_elements v) "pop not ArrayV";
      return $ Value $ LAST vs od st) k ∧
  apply_base_target cx btv st DoneK = AK cx (ApplyBaseTarget btv) st DoneK ∧
  apply_base_target cx _ st _ =
    AK cx (ApplyExc $ Error "apply_base_target k") st DoneK
End

val apply_base_target_pre_def = apply_base_target_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            bind_def, ignore_bind_def]
  |> cv_auto_trans_pre;

Theorem assign_subscripts_PopOp_not_empty:
  ∀v is ao b. ao = PopOp ∧ v = ArrayV b [] ⇒
              ISR $ assign_subscripts v is ao
Proof
  ho_match_mp_tac assign_subscripts_ind
  \\ rw[]
  \\ rw[assign_subscripts_def, oneline pop_element_def]
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
  \\ CASE_TAC \\ rw[]
  \\ gvs[replace_elements_def, extract_elements_def]
  \\ gvs[integer_index_def]
QED

Theorem apply_base_target_pre[cv_pre]:
  apply_base_target_pre cx btv st v
Proof
  rw[apply_base_target_pre_def]
  \\ Cases_on`btv` \\ gvs[]
  \\ simp[lift_option_def]
  \\ qmatch_goalsub_rename_tac`extract_elements a`
  \\ Cases_on`a` \\ gvs[extract_elements_def, raise_def, return_def]
  \\ rpt strip_tac \\ gvs[]
  \\ qmatch_asmsub_rename_tac`get_Value tv`
  \\ Cases_on`tv` \\ gvs[raise_def, return_def]
  \\ qmatch_asmsub_rename_tac`BaseTargetV loc sbs`
  \\ Cases_on`loc` \\ TRY (PairCases_on`p`)
  \\ gvs[assign_target_def, bind_def, ignore_bind_def,
         CaseEq"prod", CaseEq"sum", return_def, lift_sum_def,
         lift_option_def, sum_CASE_rator, option_CASE_rator,
         CaseEq"option", raise_def, assign_toplevel_def,
         oneline sum_map_left_def]
  \\ qspecl_then[`ArrayV b []`,`REVERSE sbs`,`PopOp`]mp_tac
       assign_subscripts_PopOp_not_empty
  \\ simp[]
QED

Definition apply_target_def:
  apply_target cx gv st (AssignK e k) =
    eval_expr_cps cx e st (AssignK1 gv k) ∧
  apply_target cx gv st (TargetsK gs k) =
    eval_targets_cps cx gs st (TargetsK1 gv k) ∧
  apply_target cx gv st _ =
    AK cx (ApplyExc $ Error "apply_target k") st DoneK
End

val () = cv_auto_trans apply_target_def;

Definition apply_tv_def:
  apply_tv cx tv st (SubscriptK e k) =
    eval_expr_cps cx e st (SubscriptK1 tv k) ∧
  apply_tv cx tv st (IfK ss1 ss2 k) =
    liftk cx (K Apply) (push_scope st) (IfK1 tv ss1 ss2 k) ∧
  apply_tv cx tv st DoneK = AK cx (ApplyTv tv) st DoneK ∧
  apply_tv cx tv st k =
    liftk cx ApplyVal (get_Value tv st) k
End

val () = apply_tv_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_val_def:
  apply_val cx v st (ReturnK k) = apply_exc cx (ReturnException v) st k ∧
  apply_val cx (BoolV T) st (AssertK1 str k) = apply cx st k ∧
  apply_val cx (BoolV F) st (AssertK1 str k) =
    apply_exc cx (AssertException str) st k ∧
  apply_val cx v st (AssertK1 _ k) = apply_exc cx (Error "not BoolV") st k ∧
  apply_val cx (StringV _ str) st (AssertK e k) =
    eval_expr_cps cx e st (AssertK1 str k) ∧
  apply_val cx (StringV _ str) st (RaiseK k) =
    apply_exc cx (AssertException str) st k ∧
  apply_val cx _ st (RaiseK k) =
    apply_exc cx (Error "raise not StringV") st k ∧
  apply_val cx _ st (AssertK e k) =
    apply_exc cx (Error "assert not StringV") st k ∧
  apply_val cx v st (AnnAssignK id k) =
    liftk cx (K Apply) (new_variable id v st) k ∧
  apply_val cx v st (AssignK1 gv k) =
    liftk cx (K Apply) (assign_target cx gv (Replace v) st) k ∧
  apply_val cx v st (AugAssignK1 (loc, sbs) bop k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (Update bop v) st) k ∧
  apply_val cx v st (AppendK1 (loc, sbs) k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (AppendOp v) st) k ∧
  apply_val cx v st (ExprK k) = apply cx st k ∧
  apply_val cx v st (ArrayK k) =
    liftk cx ApplyVals
      (lift_option (extract_elements v) "For not ArrayV" st) k ∧
  apply_val cx v st (RangeK1 e k) =
    (case lift_option (dest_NumV v) "start not NumV" st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL n1, st) => eval_expr_cps cx e st (RangeK2 n1 k)) ∧
  apply_val cx v st (RangeK2 n1 k) =
    (case do n2 <- lift_option (dest_NumV v) "end not NumV";
             check (n1 < n2) "no range";
             return $ GENLIST (λn. IntV &(n1 + n)) (n2 - n1)
     od st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL vs, st) => AK cx (ApplyVals vs) st k) ∧
  apply_val cx v st (SubscriptTargetK1 (loc, sbs) k) =
    (case lift_option (value_to_key v) "SubscriptTarget value_to_key" st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL sk, st) => apply_base_target cx (loc, sk :: sbs) st k) ∧
  apply_val cx (BoolV T) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e2 st k ∧
  apply_val cx (BoolV F) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e3 st k ∧
  apply_val cx v st (IfExpK _ _ k) =
    apply_exc cx (Error "not BoolV") st k ∧
  apply_val cx v2 st (SubscriptK1 tv1 k) =
    liftk cx ApplyTv (do
      ts <- lift_option (get_self_code cx) "Subscript get_self_code";
      lift_sum (evaluate_subscript ts tv1 v2)
    od st) k ∧
  apply_val cx v st (AttributeK id k) =
    liftk cx (ApplyTv o Value) (lift_sum (evaluate_attribute v id) st) k ∧
  apply_val cx v st (ExprsK es k) =
    eval_exprs_cps cx es st (ExprsK1 v k) ∧
  apply_val cx v st DoneK = AK cx (ApplyVal v) st DoneK ∧
  apply_val cx v st _ =
    AK cx (ApplyExc $ Error "apply_val k") st DoneK
End

val () = apply_val_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, lift_option_def, lift_sum_def,
            bind_def, ignore_bind_def]
  |> cv_auto_trans;

Definition apply_vals_def:
  apply_vals cx vs st (ExprsK1 v k) =
    apply_vals cx (v::vs) st k ∧
  apply_vals cx vs st (ForK id n body k) =
    (case do check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
             return vs od st
     of (INR ex, st) => apply_exc cx ex st k
      | (INL vs, st) => eval_for_cps cx (string_to_num id) body vs st k) ∧
  apply_vals cx vs st (ArrayLitK b k) =
    apply_tv cx (Value $ ArrayV b vs) st k ∧
  apply_vals cx vs st (StructLitK ks k) =
    apply_tv cx (Value $ StructV (ZIP (ks, vs))) st k ∧
  apply_vals cx vs st (BuiltinK bt k) =
    liftk cx ApplyTv (do
      acc <- get_accounts;
      v <- lift_sum $ evaluate_builtin cx acc bt vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (LogK id k) =
    liftk cx (K Apply) (push_log (id, vs) st) k ∧
  apply_vals cx vs st (CallSendK k) =
    liftk cx ApplyTv (do
      check (LENGTH vs = 2) "CallSendK nargs";
      toAddr <- lift_option (dest_AddressV $ EL 0 vs) "Send not AddressV";
      amount <- lift_option (dest_NumV $ EL 1 vs) "Send not NumV";
      transfer_value cx.txn.sender toAddr amount;
      return $ Value NoneV
    od st) k ∧
  apply_vals cx vs st (IntCallK fn args body k) =
    (case do
      env <- lift_option (bind_arguments args vs) "IntCall bind_arguments";
      prev <- get_scopes;
      cxf <- push_function fn env cx;
      return (prev, cxf, body) od st
     of (INR ex, st) => apply_exc cx ex st k
      | (INL (prev, cxf, body), st) =>
          eval_stmts_cps cxf body st (IntCallK1 prev k)) ∧
  apply_vals cx vs st DoneK = AK cx (ApplyVals vs) st DoneK ∧
  apply_vals cx vs st _ =
    AK cx (ApplyExc $ Error "apply_vals k") st DoneK
End

val apply_vals_pre_def = apply_vals_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, lift_option_def,
            lift_sum_def, prod_CASE_rator,
            sum_CASE_rator, option_CASE_rator]
  |> cv_auto_trans_pre;

Theorem apply_vals_pre[cv_pre]:
  ∀a b c d. apply_vals_pre a b c d
Proof
  ho_match_mp_tac apply_vals_ind \\ rw[]
  \\ rw[Once apply_vals_pre_def]
  \\ gvs[check_def, assert_def]
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
  (∀cx nm body vs st k.
     cont (eval_for_cps cx nm body vs st k) =
     cont ((
       case eval_for cx nm body vs st
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
Proof
  ho_match_mp_tac evaluate_ind
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, return_def]
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- (
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
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ reverse (Cases_on `x`) \\ simp[switch_BoolV_def, raise_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[return_def, Once OWHILE_THM, stepk_def]
    \\ Cases_on`v`
    \\ simp[dest_StringV_def, lift_option_def, return_def,
            raise_def, apply_val_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM] )
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC
    \\ CASE_TAC \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ qmatch_goalsub_rename_tac`dest_StringV v`
    \\ first_x_assum $ drule_then drule
    \\ rw[cont_def]
    \\ CASE_TAC \\ CASE_TAC \\ gvs[]
    \\ BasicProvers.TOP_CASE_TAC \\ gvs[]
    \\ pop_assum mp_tac
    \\ reverse BasicProvers.TOP_CASE_TAC \\ gvs[]
    \\ strip_tac \\ gvs[]
    >- (
      Cases_on`v` \\ gvs[dest_StringV_def, lift_option_def, raise_def,
                         apply_val_def, return_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM] )
    \\ Cases_on`v` \\ gvs[dest_StringV_def, lift_option_def, raise_def,
                       apply_val_def, return_def]
    \\ pop_assum mp_tac
    \\ reverse CASE_TAC \\ strip_tac \\ gvs[]
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def] \\ gvs[apply_tv_def, liftk1, return_def]
    \\ qmatch_goalsub_rename_tac`get_Value v`
    \\ Cases_on`v` \\ gvs[return_def, raise_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def]
    \\ gvs[switch_BoolV_def, raise_def]
    \\ pop_assum mp_tac
    \\ reverse(rw[return_def, raise_def]) \\ rw[apply_val_def]
    >- (
      qmatch_goalsub_rename_tac`apply_val _ v`
      \\ Cases_on`v` \\ rw[apply_val_def]
      \\ rw[Once OWHILE_THM, stepk_def, SimpRHS] \\ gvs[]
      \\ rw[apply_exc_def, Once OWHILE_THM] )
    \\ rw[Once OWHILE_THM, stepk_def, SimpRHS] \\ gvs[]
    \\ rw[Once OWHILE_THM, apply_def, apply_exc_def] )
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def, liftk1])
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ reverse CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, liftk1, apply_val_def] )
  \\ conj_tac >- (
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
  \\ conj_tac >- (
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
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ qmatch_goalsub_rename_tac`AugAssignK1 p` \\ Cases_on`p`
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
  \\ conj_tac >- (
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
    \\ qmatch_goalsub_abbrev_tac`Error str`
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
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
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
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ rw[ignore_bind_def, bind_def, return_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_val_def]
    \\ gvs[] \\ rw[apply_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- rw[eval_stmts_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
    rw[eval_stmts_cps_def, evaluate_def, return_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_def]
    \\ gvs[]
    \\ first_x_assum drule \\ rw[])
  \\ conj_tac >- (
    rw[eval_iterator_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- (
    rw[eval_iterator_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ gvs[]
    \\ first_x_assum $ funpow 2 drule_then drule
    \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ gvs[return_def, bind_def, ignore_bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
    \\ gvs[apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
  \\ conj_tac >- (
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- (
    rw[eval_target_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_targets_def, return_def] )
  \\ conj_tac >- rw[eval_target_cps_def, evaluate_def, bind_def, return_def]
  \\ conj_tac >- (
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_target_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_targets_def] )
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, liftk1]
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
    rw[eval_base_target_cps_def, evaluate_def, bind_def, UNCURRY, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- (
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
      gvs[lift_option_def, option_CASE_rator, CaseEq"option",
          raise_def, return_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
    \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- rw[eval_for_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
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
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1]
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1]
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1]
  \\ conj_tac >- (
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
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[return_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def]
    \\ gvs[]
    \\ simp[apply_tv_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, bind_def, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def]
    \\ gvs[]
    \\ simp[apply_tv_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- (
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
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def, bind_def, liftk1] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ rw[return_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def, liftk1])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, raise_def, bind_def, liftk1])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, raise_def, bind_def, liftk1])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def,
          bind_def, ignore_bind_def, liftk1]
    \\ qmatch_goalsub_abbrev_tac`check b c d`
    \\ `check b c d = (INL (), d)`
    by (
      rw[check_def, assert_def, Abbr`b`]
      \\ drule eval_exprs_length
      \\ gvs[check_def, assert_def] )
    \\ rw[] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def,
       no_recursion_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- CASE_TAC
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- CASE_TAC
    \\ CASE_TAC
    \\ reverse CASE_TAC
    >- CASE_TAC
    \\ CASE_TAC
    \\ rw[return_def]
    \\ gvs[]
    \\ first_assum (drule_then (drule_then (drule_then drule)))
    \\ simp_tac std_ss [] \\ disch_then kall_tac
    \\ CASE_TAC
    \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def]
    \\ CASE_TAC
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- (
      CASE_TAC
      \\ rw[Once OWHILE_THM, stepk_def, SimpRHS]
      \\ gvs[apply_exc_def] \\ rw[Once OWHILE_THM] )
    \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, SimpRHS]
      \\ gvs[apply_exc_def] \\ rw[Once OWHILE_THM] )
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, SimpRHS]
      \\ gvs[apply_exc_def] \\ rw[Once OWHILE_THM] )
    \\ rw[return_def, finally_def, try_def, bind_def]
    \\ last_x_assum $ funpow 7 drule_then drule
    \\ simp_tac std_ss [] \\ disch_then kall_tac
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, liftk1, finally_def]
      \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC
      \\ gvs[ignore_bind_def, bind_def, pop_function_def, return_def,
             set_scopes_def, lift_option_def, option_CASE_rator, CaseEq"option",
             raise_def, push_function_def, o_DEF] )
    \\ rw[Once OWHILE_THM, stepk_def, apply_def, liftk1]
    \\ CASE_TAC
    \\ reverse CASE_TAC
    \\ gvs[push_function_def, return_def, o_DEF] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def]
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
  fromk _ = (INR $ Error "fromk", empty_state)
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

val cont_tr_pre_def = cv_trans_pre cont_tr;

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
  fromtvk _ = (INR $ Error "fromtvk", empty_state)
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
  |> cv_auto_trans_pre;

Theorem constants_env_pre[cv_pre]:
  ∀x. constants_env_pre x
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

val call_external_function_pre_def = call_external_function_def
     |> SRULE [eval_stmts_eq_cont_cps]
     |> cv_auto_trans_pre;

Theorem call_external_function_pre[cv_pre]:
  call_external_function_pre am cx ts args vals body
Proof
  rw[call_external_function_pre_def]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_stmts_cps cx ss st k`
  \\ qspecl_then[`cx`,`ss`,`st`,`k`]mp_tac  $ cj 2 eval_cps_eq
  \\ rw[]
  \\ CASE_TAC
  \\ CASE_TAC
  \\ rw[Abbr`k`, cont_def]
  \\ rw[Once OWHILE_THM]
QED

val () = cv_auto_trans call_external_def;

val () = cv_auto_trans load_contract_def;

val () = export_theory();
