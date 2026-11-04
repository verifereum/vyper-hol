(* Actual internal-call body exception transport. *)
Theory gasIntCallBody
Ancestors
  gasExemptCert gasSummary gasSummaryCompose fragGasFocus
  vyperCall vyperState vyperInterpreter vyperContext vyperValue vyperAST
  venomState list
Libs
  monadsyntax

Theorem gas_exempt_intcall_body:
  !memory tops ctx func cx ty src fn args drv es s0 left values mid t
   ts mut params ret body env tv invoke callee entered right err ee leaf finish.
    ~MEM (src, fn) cx.stk /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut, F, params, [], ret, body) /\
    LENGTH args = LENGTH params /\
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr_results cx args) (read_results cx))
      (es, s0) left (INL values) mid (OK t) /\
    bind_arguments (get_tenv cx) params values = SOME env /\
    evaluate_type (get_tenv cx) ret = SOME tv /\
    gas_marked_exec memory (ctx, func) (set_scopes [env])
      (mid with gas_obs := [], t) [] (INL ())
      (mid with scopes := [env]) (OK invoke) /\
    gas_invoke_entry (ctx, func) invoke callee entered /\
    gas_exempt_cert memory tops (ctx, callee)
      (ignore_bind
        (eval_stmts (cx with stk updated_by CONS (src, fn)) body) (return ()))
      ((mid with scopes := [env]) with gas_obs := [], entered)
      right (err, ee) (leaf, finish) ==>
    gas_exempt_cert memory tops (ctx, func)
      (ignore_bind (eval_expr cx (Call ty (IntCall (src, fn)) args drv))
        (return ()))
      (es, s0) (left ++ right)
      (err, ee with scopes := mid.scopes) (leaf, finish)
Proof
  cheat
QED
