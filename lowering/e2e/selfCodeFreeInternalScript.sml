(* Lookup closure and guarded internal-call congruence. *)
Theory selfCodeFreeInternal
Ancestors
  selfCodeFreeInvariant selfCodeFreeContext selfCodeFreeSyntax vyperInterpreter
  vyperContext vyperState supportedExprTraverse supportedStmtTraverse
Libs monadsyntax

val _ = Parse.hide "body";
val _ = monadsyntax.enable_monad "vyper_evaluation";
val _ = temp_delsimps ["lock_if_nr_def", "unlock_if_nr_def"];

Theorem self_code_free_context_callable:
  self_code_free_context cx /\ get_module_code cx sid = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) ==>
  ~supported_exprs_exists is_self_code dflts /\
  ~supported_stmts_expr_exists is_self_code body
Proof
  simp[self_code_free_context_def] >> strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  drule_all lookup_callable_function_self_code_free >> simp[]
QED


Theorem type_check_conditional[local]:
  type_check b msg = if b then return () else raise (Error (TypeError msg))
Proof
  Cases_on `b` >> simp[FUN_EQ_THM, type_check_def, assert_def, return_def, raise_def]
QED

Theorem self_code_free_int_call:
  (!ts mut nr args dflts ret body.
    ~MEM (sid,fn) cx.stk /\ get_module_code cx sid = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
    LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts ==>
    eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es) /\
  (!ts mut nr args dflts ret body s vs t.
    ~MEM (sid,fn) cx.stk /\ get_module_code cx sid = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
    LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts /\
    eval_exprs cx es s = (INL vs,t) ==>
    eval_exprs ((cx with stk updated_by CONS (sid,fn)) with txn := (cx.txn with code := c))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) =
    eval_exprs (cx with stk updated_by CONS (sid,fn))
      (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
  (!ts mut nr args dflts ret body s vs t prev u dvs v env rtv w z.
    ~MEM (sid,fn) cx.stk /\ get_module_code cx sid = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
    LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts /\
    eval_exprs cx es s = (INL vs,t) /\
    finally (do set_scopes [FEMPTY];
      eval_exprs (cx with stk updated_by CONS (sid,fn))
        (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) od)
      (set_scopes prev) u = (INL dvs,v) /\
    bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME env /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    lock_if_nr cx nr (is_view_mut mut) w = (INL (),z) ==>
    eval_stmts ((cx with stk updated_by CONS (sid,fn)) with txn := (cx.txn with code := c)) body =
    eval_stmts (cx with stk updated_by CONS (sid,fn)) body) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (IntCall (sid,fn)) es kws) =
  eval_expr cx (Call ty (IntCall (sid,fn)) es kws)
Proof
  strip_tac >> once_rewrite_tac[evaluate_def] >> simp[] >>
  Cases_on `MEM (sid,fn) cx.stk`
  >- simp[type_check_conditional, FUN_EQ_THM, ignore_bind_def, bind_def, raise_def] >>
  simp[type_check_conditional, ignore_bind_def, bind_return] >>
  Cases_on `get_module_code cx sid`
  >- simp[lift_option_type_def, FUN_EQ_THM, bind_def, raise_def] >>
  simp[lift_option_type_def, bind_return] >>
  rename1 `get_module_code cx sid = SOME ts` >>
  Cases_on `lookup_callable_function cx.in_deploy fn ts`
  >- simp[lift_option_type_def, FUN_EQ_THM, bind_def, raise_def] >>
  simp[lift_option_type_def, bind_return] >>
  rename1 `lookup_callable_function cx.in_deploy fn ts = SOME tup` >> PairCases_on `tup` >> simp[] >>
  reverse (Cases_on `LENGTH es <= LENGTH tup2 /\ LENGTH tup2 - LENGTH es <= LENGTH tup3`)
  >- simp[type_check_conditional, FUN_EQ_THM, bind_def, raise_def] >>
  gvs[type_check_conditional, bind_return, ignore_bind_def] >>
  irule bind_cong_implicit >> simp[] >> rpt strip_tac >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!s vs t. _ ==> _` (drule_then assume_tac) >> simp[] >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  Cases_on `bind_arguments (get_tenv cx) tup2 (x ++ x'')`
  >- simp[bind_def, raise_def] >> simp[bind_return] >>
  Cases_on `evaluate_type (get_tenv cx) tup4`
  >- simp[bind_def, raise_def] >> simp[bind_return] >>
  irule bind_cong >> simp[] >> rpt strip_tac >>
  simp[push_function_def, return_def, bind_def] >>
  gvs[] >> first_x_assum (drule_all_then assume_tac) >> simp[]
QED
