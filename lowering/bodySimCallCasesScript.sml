(*
 * The body simulation of S1: the call expression cases (#636, #638)
 *
 * The cases of evaluate_ind for internal and external calls, raw calls,
 * raw_log, raw_revert, selfdestruct and create, split from
 * bodySimExprCases so they can be worked on apart from the other
 * expression cases.  Each but create and selfdestruct is its piece in a
 * leaf theory bodySimCall*; those two hold vacuously (expr_body_pre
 * excludes them).
 *)

Theory bodySimCallCases
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph
  bodySimCallExtcall bodySimCallIntcall bodySimCallRawCall
  bodySimCallRawCallCalldata bodySimCallRawLog bodySimCallRawRevert

Theorem body_extcall_case:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ok cx (TAKE 1 es) ==>
    body_expr_ok cx (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  ACCEPT_TAC extcall_body_expr_ok
QED

Theorem body_intcall_case:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8' s'11' rtv
         t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' x'' t'6'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       set_scopes [FEMPTY] s'8' = (INL x'',t'6') ==>
       body_exprs_ok cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_results_ok cx es) ==>
    body_expr_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  ACCEPT_TAC intcall_body_expr_ok
QED

Theorem body_raw_call_case:
  !cx ty flags es v18.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  ACCEPT_TAC raw_call_body_expr_ok
QED

Theorem body_raw_call_calldata_case:
  !cx ty flags es v19.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  ACCEPT_TAC raw_call_calldata_body_expr_ok
QED

Theorem body_raw_log_case:
  !cx v20 es v21.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v20 RawLog es v21)
Proof
  ACCEPT_TAC raw_log_body_expr_ok
QED

Theorem body_raw_revert_case:
  !cx v22 es v23.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v22 RawRevert es v23)
Proof
  ACCEPT_TAC raw_revert_body_expr_ok
QED

Theorem body_selfdestruct_case:
  !cx v24 es v25.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >>
  rw[exprSimHypsDefsTheory.expr_body_pre_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.expr_evm_run_root_def]
QED

Theorem body_create_case:
  !cx ty kind has_salt rof kw_order es v26.
    (!raw_args s'' prefix t s'3' code_size t'.
       kind = CreateFromBlueprint raw_args /\
       eval_exprs cx (TAKE (if has_salt then 4 else 3) es) s'' = (INL prefix,t) /\
       check_create_blueprint has_salt prefix s'3' = (INL code_size,t') ==>
       body_results_ok cx (DROP (if has_salt then 4 else 3) es)) /\
    (!raw_args.
       kind = CreateFromBlueprint raw_args ==>
       body_exprs_ok cx (TAKE (if has_salt then 4 else 3) es)) /\
    (!s'' prefix t ctor_es nargs s'3' results t' s'4' args t''.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) /\
       eval_expr_results cx (TAKE nargs ctor_es) s'3' = (INL results,t') /\
       read_results cx results s'4' = (INL args,t'') ==>
       body_exprs_ok cx (DROP nargs ctor_es)) /\
    (!s'' prefix t ctor_es nargs.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) ==>
       body_results_ok cx (TAKE nargs ctor_es)) /\
    (kind = CreateCopyOf ==> body_exprs_ok cx es) /\
    (kind = CreateMinimalProxy ==> body_exprs_ok cx es) /\
    (kind = RawCreate ==> body_exprs_ok cx (TAKE 2 es)) ==>
    body_expr_ok cx (Call ty (CreateTarget kind has_salt rof kw_order) es v26)
Proof
  rpt strip_tac >> irule body_expr_ok_intro >>
  rw[exprSimHypsDefsTheory.expr_body_pre_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.expr_evm_run_root_def]
QED
