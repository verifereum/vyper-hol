(* Non-call branches of transaction-code congruence. *)
Theory selfCodeFreeStructural
Ancestors
  selfCodeFreeInvariant selfCodeFreeContext selfCodeFreeSyntax vyperInterpreter
  vyperContext supportedStmtTraverse supportedExprTraverse e2eProducers
Libs monadsyntax

val _ = Parse.hide "body";
val _ = monadsyntax.enable_monad "vyper_evaluation";

Theorem self_code_free_raise_custom:
  (!id positional kwargs tops params es.
    err = CustomError id positional kwargs /\
    get_module_code cx (FST id) = SOME tops /\
    lookup_custom_error_args_in (SND id) tops = SOME params /\
    order_custom_error_args params err = SOME es ==>
    !c. ~supported_exprs_exists is_self_code es ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) /\
  ~supported_exprs_exists is_self_code (custom_error_exprs err) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (Raise (RaiseCustomError err)) =
  eval_stmt cx (Raise (RaiseCustomError err))
Proof
  strip_tac >> Cases_on `err` >> rename1 `CustomError id positional kwargs` >>
  once_rewrite_tac[evaluate_def] >> simp[] >>
  Cases_on `get_module_code cx (FST id)` >> simp[] >>
  rename1 `SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND id) tops` >> simp[] >>
  rename1 `SOME params` >>
  Cases_on `order_custom_error_args params (CustomError id positional kwargs)` >> simp[] >>
  drule_all supported_exprs_exclusion_custom_error >> strip_tac >>
  gvs[] >> first_x_assum (drule_all_then (qspec_then `c` mp_tac)) >> simp[]
QED

Theorem self_code_free_assert_reason:
  (!c. eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e) /\
  (!s tv t. eval_expr cx e s = (INL tv,t) ==>
    !c. eval_expr (cx with txn := (cx.txn with code := c)) se = eval_expr cx se) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (Assert e (AssertReason se)) =
  eval_stmt cx (Assert e (AssertReason se))
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then (qspec_then `c` assume_tac)) >> simp[]
QED

Theorem self_code_free_assert_custom:
  (!c. eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e) /\
  (!s tv t id positional kwargs tops params es.
    eval_expr cx e s = (INL tv,t) /\
    err = CustomError id positional kwargs /\
    get_module_code cx (FST id) = SOME tops /\
    lookup_custom_error_args_in (SND id) tops = SOME params /\
    order_custom_error_args params err = SOME es ==>
    !c. ~supported_exprs_exists is_self_code es ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) /\
  ~supported_exprs_exists is_self_code (custom_error_exprs err) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (Assert e (AssertCustomError err)) =
  eval_stmt cx (Assert e (AssertCustomError err))
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  `eval_stmt (cx with txn := (cx.txn with code := c)) (Raise (RaiseCustomError err)) =
   eval_stmt cx (Raise (RaiseCustomError err))` by
    (irule self_code_free_raise_custom >> simp[] >> rpt strip_tac >>
     first_x_assum (drule_all_then (qspec_then `c` mp_tac)) >> simp[]) >>
  pop_assum mp_tac >> once_rewrite_tac[evaluate_def] >> simp[] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem self_code_free_append:
  eval_target_place (cx with txn := (cx.txn with code := c)) bt = eval_target_place cx bt /\
  (!s p t. eval_target_place cx bt s = (INL p,t) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (Append bt e) =
  eval_stmt cx (Append bt e)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_assign:
  eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e /\
  (!s r t u v w. eval_expr cx e s = (INL r,t) /\
    read_result cx r u = (INL v,w) ==>
    eval_target_place (cx with txn := (cx.txn with code := c)) bt = eval_target_place cx bt) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (Assign (BaseTarget bt) e) =
  eval_stmt cx (Assign (BaseTarget bt) e)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_augassign:
  eval_target_place (cx with txn := (cx.txn with code := c)) bt = eval_target_place cx bt /\
  (!s p t u cur w a ptv b.
    eval_target_place cx bt s = (INL p,t) /\
    read_place cx p u = (INL cur,w) /\ place_type_value cx p a = (INL ptv,b) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (AugAssign ty bt bop e) =
  eval_stmt cx (AugAssign ty bt bop e)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_assign_tuple:
  eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e /\
  (!s r t u v w. eval_expr cx e s = (INL r,t) /\ read_result cx r u = (INL v,w) ==>
    assign_tuple_targets (cx with txn := (cx.txn with code := c)) (TupleTarget gs) v =
    assign_tuple_targets cx (TupleTarget gs) v) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (Assign (TupleTarget gs) e) =
  eval_stmt cx (Assign (TupleTarget gs) e)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_stmts_cons:
  eval_stmt (cx with txn := (cx.txn with code := c)) s = eval_stmt cx s /\
  (!st x rt. eval_stmt cx s st = (INL x,rt) ==>
    eval_stmts (cx with txn := (cx.txn with code := c)) ss = eval_stmts cx ss) ==>
  eval_stmts (cx with txn := (cx.txn with code := c)) (s::ss) = eval_stmts cx (s::ss)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule ignore_bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_expr_results_cons:
  eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e /\
  (!st x rt. eval_expr cx e st = (INL x,rt) ==>
    eval_expr_results (cx with txn := (cx.txn with code := c)) es = eval_expr_results cx es) ==>
  eval_expr_results (cx with txn := (cx.txn with code := c)) (e::es) =
  eval_expr_results cx (e::es)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_exprs_cons:
  eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e /\
  (!st r rt u v w. eval_expr cx e st = (INL r,rt) /\ read_result cx r u = (INL v,w) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) ==>
  eval_exprs (cx with txn := (cx.txn with code := c)) (e::es) = eval_exprs cx (e::es)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_targets_cons:
  assign_tuple_targets (cx with txn := (cx.txn with code := c)) g v = assign_tuple_targets cx g v /\
  (!st x rt. assign_tuple_targets cx g v st = (INL x,rt) ==>
    assign_tuple_target_list (cx with txn := (cx.txn with code := c)) gs vs =
    assign_tuple_target_list cx gs vs) ==>
  assign_tuple_target_list (cx with txn := (cx.txn with code := c)) (g::gs) (v::vs) =
  assign_tuple_target_list cx (g::gs) (v::vs)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule ignore_bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_base_subscript:
  eval_base_place (cx with txn := (cx.txn with code := c)) bt = eval_base_place cx bt /\
  (!st r rt. eval_base_place cx bt st = (INL r,rt) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e) ==>
  eval_base_place (cx with txn := (cx.txn with code := c)) (SubscriptTarget bt e) =
  eval_base_place cx (SubscriptTarget bt e)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_annassign:
  (!st tyv rt.
    lift_option_type (evaluate_type (get_tenv cx) typ) "AnnAssign evaluate_type" st = (INL tyv,rt) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (AnnAssign id typ e) =
  eval_stmt cx (AnnAssign id typ e)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_iterator_range:
  eval_expr (cx with txn := (cx.txn with code := c)) a = eval_expr cx a /\
  (!st r rt u v w. eval_expr cx a st = (INL r,rt) /\ read_result cx r u = (INL v,w) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) b = eval_expr cx b) ==>
  eval_iterator (cx with txn := (cx.txn with code := c)) (Range a b) =
  eval_iterator cx (Range a b)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_for_stmt:
  (!st tyv rt.
    lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" st = (INL tyv,rt) ==>
    eval_iterator (cx with txn := (cx.txn with code := c)) it = eval_iterator cx it) /\
  (!st tyv rt u vs w a x b.
    lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type" st = (INL tyv,rt) /\
    eval_iterator cx it u = (INL vs,w) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" a = (INL x,b) ==>
    eval_for (cx with txn := (cx.txn with code := c)) tyv id body vs =
    eval_for cx tyv id body vs) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (For id typ it n body) =
  eval_stmt cx (For id typ it n body)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  `eval_iterator (cx with txn := (cx.txn with code := c)) it = eval_iterator cx it`
    by metis_tac[] >> simp[] >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  irule ignore_bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_for_cons:
  (!s0 v s1 st x rt. read_result cx r s0 = (INL v,s1) /\
    push_scope_with_var nm tyv v st = (INL x,rt) ==>
    eval_stmts (cx with txn := (cx.txn with code := c)) body = eval_stmts cx body) /\
  (!s0 v s1 st x rt u broke w.
    read_result cx r s0 = (INL v,s1) /\
    push_scope_with_var nm tyv v st = (INL x,rt) /\
    finally (try (do eval_stmts cx body; return F od) handle_loop_exception)
      pop_scope u = (INL broke,w) /\ ~broke ==>
    eval_for (cx with txn := (cx.txn with code := c)) tyv nm body vs =
    eval_for cx tyv nm body vs) ==>
  eval_for (cx with txn := (cx.txn with code := c)) tyv nm body (r::vs) =
  eval_for cx tyv nm body (r::vs)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule ignore_bind_cong >> simp[] >> rpt strip_tac >>
  `eval_stmts (cx with txn := (cx.txn with code := c)) body = eval_stmts cx body`
    by metis_tac[] >> simp[] >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[] >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_if_stmt:
  eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e /\
  (!st r rt u x w. eval_expr cx e st = (INL r,rt) /\ push_scope u = (INL x,w) ==>
    eval_stmts (cx with txn := (cx.txn with code := c)) yes = eval_stmts cx yes) /\
  (!st r rt u x w. eval_expr cx e st = (INL r,rt) /\ push_scope u = (INL x,w) ==>
    eval_stmts (cx with txn := (cx.txn with code := c)) no = eval_stmts cx no) ==>
  eval_stmt (cx with txn := (cx.txn with code := c)) (If e yes no) = eval_stmt cx (If e yes no)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule ignore_bind_cong >> simp[] >> rpt strip_tac >>
  `eval_stmts (cx with txn := (cx.txn with code := c)) yes = eval_stmts cx yes` by metis_tac[] >>
  `eval_stmts (cx with txn := (cx.txn with code := c)) no = eval_stmts cx no` by metis_tac[] >>
  simp[]
QED

Theorem self_code_free_if_expr:
  eval_expr (cx with txn := (cx.txn with code := c)) e = eval_expr cx e /\
  (!st r rt. eval_expr cx e st = (INL r,rt) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) yes = eval_expr cx yes) /\
  (!st r rt. eval_expr cx e st = (INL r,rt) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) no = eval_expr cx no) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (IfExp ty e yes no) =
  eval_expr cx (IfExp ty e yes no)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  `eval_expr (cx with txn := (cx.txn with code := c)) yes = eval_expr cx yes` by metis_tac[] >>
  `eval_expr (cx with txn := (cx.txn with code := c)) no = eval_expr cx no` by metis_tac[] >>
  simp[]
QED

Theorem self_code_free_subscript:
  eval_expr (cx with txn := (cx.txn with code := c)) a = eval_expr cx a /\
  (!st r rt u r' w.
    eval_expr cx a st = (INL r,rt) /\
    (if subscript_reads_base cx a b then
       do v <- read_result cx r; return (Value v) od else return r) u = (INL r',w) ==>
    eval_expr (cx with txn := (cx.txn with code := c)) b = eval_expr cx b) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Subscript ty a b) =
  eval_expr cx (Subscript ty a b)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_all_then assume_tac) >> simp[]
QED

Theorem self_code_free_type_builtin:
  (!st x rt.
    type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" st = (INL x,rt) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (TypeBuiltin ty tb typ es) =
  eval_expr cx (TypeBuiltin ty tb typ es)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  irule ignore_bind_cong_implicit >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem self_code_free_tuple_target:
  (!vs. v = ArrayV (TupleV vs) ==>
    assign_tuple_target_list (cx with txn := (cx.txn with code := c)) gs vs =
    assign_tuple_target_list cx gs vs) ==>
  assign_tuple_targets (cx with txn := (cx.txn with code := c)) (TupleTarget gs) v =
  assign_tuple_targets cx (TupleTarget gs) v
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >>
  Cases_on `v` >> simp[] >> rename1 `ArrayV av` >> Cases_on `av` >> simp[]
QED

Theorem self_code_free_struct:
  (~supported_exprs_exists is_self_code (MAP SND fields) ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) (MAP SND fields) =
    eval_exprs cx (MAP SND fields)) /\
  ~supported_fields_exists is_self_code fields ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (StructLit ty id fields) =
  eval_expr cx (StructLit ty id fields)
Proof
  strip_tac >>
  `~supported_exprs_exists is_self_code (MAP SND fields)` by
    gvs[supported_exprs_exists_every, supported_fields_exists_every, listTheory.EXISTS_MAP, combinTheory.o_DEF] >>
  Cases_on `id` >> once_rewrite_tac[evaluate_def] >> simp[]
QED
