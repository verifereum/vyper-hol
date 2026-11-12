(* The cases of bodySimPtrMainAt's induction, the (D, lo) ports of the
 * bodyPtr*Cases and leaf theorems of the runtime tower (bodySimPtrMain):
 * each at a frame whose dead bytes and bound dead_lo_ok fixes, a
 * constructor's included.  Every case is admitted until its port lands;
 * the runtime twin named in its comment is the proof to port.
 *
 * TOP-LEVEL: body_expr_ptr_ok_at_leaf and the body_*_case_ptr_at cases.
 *)
Theory bodyPtrCasesAt
Ancestors
  bodyPtrPredsAt bodyPtrDefs bodySim vyperAST vyperInterpreter vyperState
  vyperValue list

val _ = Parse.hide "body";

(* Admitted: the (D, lo) port of body_expr_ptr_ok_leaf (bodySimPtrMain),
   through exprSimPtr's leaf_expr_sim_ptr. *)
Theorem body_expr_ptr_ok_at_leaf:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_ptr_ok_at cx e
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_annassign_case_ptr
   (bodyPtrAssignCases). *)
Theorem body_annassign_case_ptr_at:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_ptr_ok_at cx e) ==>
    body_stmt_ptr_ok_at cx (AnnAssign id typ e)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_append_case_ptr
   (bodyPtrLogCases). *)
Theorem body_append_case_ptr_at:
  !cx t e.
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_ptr_ok_at cx e) /\
    body_base_target_ptr_ok_at cx t ==>
    body_stmt_ptr_ok_at cx (Append t e)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_assert_case_ptr
   (bodyPtrExitCases). *)
Theorem body_assert_case_ptr_at:
  !cx e. body_expr_ptr_ok_at cx e ==> body_stmt_ptr_ok_at cx (Assert e AssertBare)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_assert_reason_case_ptr
   (bodyPtrExitCases). *)
Theorem body_assert_reason_case_ptr_at:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ptr_ok_at cx se) /\
    body_expr_ptr_ok_at cx e ==>
    body_stmt_ptr_ok_at cx (Assert e (AssertReason se))
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_assert_unreachable_case_ptr
   (bodyPtrExitCases). *)
Theorem body_assert_unreachable_case_ptr_at:
  !cx e.
    body_expr_ptr_ok_at cx e ==> body_stmt_ptr_ok_at cx (Assert e AssertUnreachable)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_assign_case_ptr
   (bodyPtrAssignCases). *)
Theorem body_assign_case_ptr_at:
  !cx t e.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_ptr_ok_at cx t) /\
    body_expr_ptr_ok_at cx e ==>
    body_stmt_ptr_ok_at cx (Assign (BaseTarget t) e)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_assign_tuple_case_ptr
   (bodyPtrAssignCases). *)
Theorem body_assign_tuple_case_ptr_at:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ptr_ok_at cx (TupleTarget gs) v) /\ body_expr_ptr_ok_at cx e ==>
    body_stmt_ptr_ok_at cx (Assign (TupleTarget gs) e)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_attribute_case_ptr
   (bodyPtrExprCases). *)
Theorem body_attribute_case_ptr_at:
  !cx v9 e id. body_expr_ptr_ok_at cx e ==> body_expr_ptr_ok_at cx (Attribute v9 e id)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_augassign_case_ptr
   (bodyPtrAssignCases). *)
Theorem body_augassign_case_ptr_at:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ptr_ok_at cx e) /\ body_base_target_ptr_ok_at cx t ==>
    body_stmt_ptr_ok_at cx (AugAssign ty t bop e)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_break_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_break_case_ptr_at:
  !cx. body_stmt_ptr_ok_at cx Break
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_builtin_case_ptr
   (bodyPtrExprCases). *)
Theorem body_builtin_case_ptr_at:
  !cx ty bt es.
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_ptr_ok_at cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_ptr_ok_at cx (HD es)) ==>
    body_expr_ptr_ok_at cx (Builtin ty bt es)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_continue_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_continue_case_ptr_at:
  !cx. body_stmt_ptr_ok_at cx Continue
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_create_case_ptr
   (bodyPtrCallCases). *)
Theorem body_create_case_ptr_at:
  !cx ty kind has_salt rof v26 es v27.
    (!raw_args s'' prefix t s'3' code_size t'.
       kind = CreateFromBlueprint raw_args /\
       eval_exprs cx (TAKE (if has_salt then 4 else 3) es) s'' =
       (INL prefix,t) /\
       check_create_blueprint has_salt prefix s'3' = (INL code_size,t') ==>
       body_results_ptr_ok_at cx (DROP (if has_salt then 4 else 3) es)) /\
    (!raw_args.
       kind = CreateFromBlueprint raw_args ==>
       body_exprs_ptr_ok_at cx (TAKE (if has_salt then 4 else 3) es)) /\
    (!s'' prefix t ctor_es nargs s'3' results t' s'4' args t''.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) /\
       eval_expr_results cx (TAKE nargs ctor_es) s'3' = (INL results,t') /\
       read_results cx results s'4' = (INL args,t'') ==>
       body_exprs_ptr_ok_at cx (DROP nargs ctor_es)) /\
    (!s'' prefix t ctor_es nargs.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) ==>
       body_results_ptr_ok_at cx (TAKE nargs ctor_es)) /\
    (kind = CreateCopyOf ==> body_exprs_ptr_ok_at cx es) /\
    (kind = CreateMinimalProxy ==> body_exprs_ptr_ok_at cx es) /\
    (kind = RawCreate ==> body_exprs_ptr_ok_at cx (TAKE 2 es)) ==>
    body_expr_ptr_ok_at cx (Call ty (CreateTarget kind has_salt rof v26) es v27)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_expr_stmt_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_expr_stmt_case_ptr_at:
  !cx e. body_expr_ptr_ok_at cx e ==> body_stmt_ptr_ok_at cx (Expr e)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_extcall_case_ptr
   (bodyPtrCallCases). *)
Theorem body_extcall_case_ptr_at:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_ptr_ok_at cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_ptr_ok_at cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ptr_ok_at cx (TAKE 1 es) ==>
    body_expr_ptr_ok_at cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_for_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_for_case_ptr_at:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ptr_ok_at cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ptr_ok_at cx it) ==>
    body_stmt_ptr_ok_at cx (For id typ it n body)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_if_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_if_case_ptr_at:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ptr_ok_at cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_ptr_ok_at cx ss2) /\ body_expr_ptr_ok_at cx e ==>
    body_stmt_ptr_ok_at cx (If e ss1 ss2)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_ifexp_case_ptr
   (bodyPtrExprCases). *)
Theorem body_ifexp_case_ptr_at:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok_at cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok_at cx e3) /\
    body_expr_ptr_ok_at cx e1 ==>
    body_expr_ptr_ok_at cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_intcall_case_ptr
   (bodyPtrIntCallCase). *)
Theorem body_intcall_case_ptr_at:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7'
         prev t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8'
         s'11' rtv t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
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
       finally do set_scopes [FEMPTY]; eval_exprs cxd needed_dflts od
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\ all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_ptr_ok_at cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7'
         prev t'5' s'8' x'' t'6'.
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
       body_exprs_ptr_ok_at cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3'.
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
       body_results_ptr_ok_at cx es) ==>
    body_expr_ptr_ok_at cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_log_case_ptr
   (bodyPtrLogCases). *)
Theorem body_log_case_ptr_at:
  !cx id es. body_exprs_ptr_ok_at cx es ==> body_stmt_ptr_ok_at cx (Log id es)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_pass_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_pass_case_ptr_at:
  !cx. body_stmt_ptr_ok_at cx Pass
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_pop_case_ptr
   (bodyPtrExprCases). *)
Theorem body_pop_case_ptr_at:
  !cx v10 bt. body_base_target_ptr_ok_at cx bt ==> body_expr_ptr_ok_at cx (Pop v10 bt)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_raise_bare_case_ptr
   (bodyPtrExitCases). *)
Theorem body_raise_bare_case_ptr_at:
  !cx. body_stmt_ptr_ok_at cx (Raise RaiseBare)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_raise_reason_case_ptr
   (bodyPtrExitCases). *)
Theorem body_raise_reason_case_ptr_at:
  !cx e. body_expr_ptr_ok_at cx e ==> body_stmt_ptr_ok_at cx (Raise (RaiseReason e))
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_raise_unreachable_case_ptr
   (bodyPtrExitCases). *)
Theorem body_raise_unreachable_case_ptr_at:
  !cx. body_stmt_ptr_ok_at cx (Raise RaiseUnreachable)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_raw_call_calldata_case_ptr
   (bodyPtrCallCases). *)
Theorem body_raw_call_calldata_case_ptr_at:
  !cx ty flags es v19.
    body_exprs_ptr_ok_at cx es ==>
    body_expr_ptr_ok_at cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_raw_call_case_ptr
   (bodyPtrCallCases). *)
Theorem body_raw_call_case_ptr_at:
  !cx ty flags es v18.
    body_exprs_ptr_ok_at cx es ==>
    body_expr_ptr_ok_at cx (Call ty (RawCallTarget flags) es v18)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_raw_log_case_ptr
   (bodyPtrCallCases). *)
Theorem body_raw_log_case_ptr_at:
  !cx v20 es v21.
    body_exprs_ptr_ok_at cx es ==> body_expr_ptr_ok_at cx (Call v20 RawLog es v21)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_raw_revert_case_ptr
   (bodyPtrCallCases). *)
Theorem body_raw_revert_case_ptr_at:
  !cx v22 es v23.
    body_exprs_ptr_ok_at cx es ==> body_expr_ptr_ok_at cx (Call v22 RawRevert es v23)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_return_case_ptr
   (bodyPtrExitCases). *)
Theorem body_return_case_ptr_at:
  !cx e. body_expr_ptr_ok_at cx e ==> body_stmt_ptr_ok_at cx (Return (SOME e))
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_return_none_case_ptr
   (bodyPtrExitCases). *)
Theorem body_return_none_case_ptr_at:
  !cx. body_stmt_ptr_ok_at cx (Return NONE)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_selfdestruct_case_ptr
   (bodyPtrCallCases). *)
Theorem body_selfdestruct_case_ptr_at:
  !cx v24 es v25.
    body_exprs_ptr_ok_at cx es ==>
    body_expr_ptr_ok_at cx (Call v24 SelfDestructTarget es v25)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_send_case_ptr
   (bodyPtrCallCases). *)
Theorem body_send_case_ptr_at:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_ptr_ok_at cx es) ==>
    body_expr_ptr_ok_at cx (Call v12 (Send has_gas) es v13)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_stmts_cons_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_stmts_cons_case_ptr_at:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_ptr_ok_at cx ss) /\
    body_stmt_ptr_ok_at cx s ==>
    body_stmts_ptr_ok_at cx (s::ss)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_stmts_nil_case_ptr
   (bodyPtrCtrlCases). *)
Theorem body_stmts_nil_case_ptr_at:
  !cx. body_stmts_ptr_ok_at cx []
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_structlit_case_ptr
   (bodyPtrExprCases). *)
Theorem body_structlit_case_ptr_at:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ptr_ok_at cx (MAP SND kes)) ==>
    body_expr_ptr_ok_at cx (StructLit v7 (src_id_opt,id) kes)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_subscript_case_ptr
   (bodyPtrExprCases). *)
Theorem body_subscript_case_ptr_at:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ptr_ok_at cx e2) /\
    body_expr_ptr_ok_at cx e1 ==>
    body_expr_ptr_ok_at cx (Subscript v8 e1 e2)
Proof
  cheat
QED

(* Admitted: the (D, lo) port of body_type_builtin_case_ptr
   (bodyPtrExprCases). *)
Theorem body_type_builtin_case_ptr_at:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_ptr_ok_at cx es) ==>
    body_expr_ptr_ok_at cx (TypeBuiltin v11 tb typ es)
Proof
  cheat
QED
