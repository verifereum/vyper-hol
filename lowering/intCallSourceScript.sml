(*
 * Internal calls: the source side (#638)
 *
 * eval_expr's IntCall case, unfolded for a call the lowering supports
 * today: every parameter given an argument (no defaults evaluated) and a
 * callee without a reentrancy lock.  The call is the recursion check, the
 * callee lookup, the argument count, the arguments, bind_arguments, the
 * body in the callee's scope (push_function), the caller's scopes back
 * (pop_function), handle_function on the body's exception, and safe_cast
 * of the result.
 *
 * TOP-LEVEL:
 *   eval_expr_intcall_unfold — the IntCall equation, from the body's result
 *)

Theory intCallSource
Ancestors
  vyperInterpreter vyperState vyperContext

Theorem eval_expr_intcall_unfold:
  !cx ty src fn es drv st ts mut args dflts ret body vs st1 env rtv.
    ~MEM (src, fn) cx.stk /\
    get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut, F, args, dflts, ret, body) /\
    LENGTH es = LENGTH args /\
    eval_exprs cx es st = (INL vs, st1) /\
    bind_arguments (get_tenv cx) args vs = SOME env /\
    evaluate_type (get_tenv cx) ret = SOME rtv ==>
    eval_expr cx (Call ty (IntCall (src, fn)) es drv) st =
    case eval_stmts (cx with stk updated_by CONS (src, fn)) body
           (st1 with scopes := [env]) of
      (INL _, st2) =>
        (do crv <- lift_option_type (safe_cast rtv NoneV) "IntCall cast ret";
            return (Value crv)
         od) (st2 with scopes := st1.scopes)
    | (INR e, st2) =>
        (do rv <- handle_function e;
            crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
            return (Value crv)
         od) (st2 with scopes := st1.scopes)
Proof
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
  simp[bind_def, ignore_bind_def, type_check_def, assert_def, return_def,
       get_scopes_def, set_scopes_def, finally_def, try_def,
       push_function_def, pop_function_def, evaluate_def] >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (src,fn)) body
              (st1 with scopes := [env])` >>
  rename1 `_ = (res, st2)` >> Cases_on `res` >>
  simp[bind_def, ignore_bind_def, return_def, set_scopes_def] >>
  rename1 `handle_function exc` >> Cases_on `exc` >>
  simp[handle_function_def, raise_def, return_def]
QED
