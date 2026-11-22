(* Request-prefix cases for the body induction. *)
Theory s1PrefixCases
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixReturnSome s1PrefixReturnNone s1PrefixExits
  s1PrefixStmtZero s1PrefixExprStmt s1PrefixNames s1PrefixLiteralWord
  s1PrefixMsgGas s1PrefixFrame stmtExprAllocationPreProps bodyInvCodeProps
  compileUnit vyperStorageTrace vyperState alist
  allocLimits allocLimitsProps bodyExprPreFacts bodySim
  exprSimHypsDefs gasContext gasShadow supportedExprs supportedStmts
  supportedExprTraverse supportedStmtTraverse
  vyperAST vyperContext vyperInterpreter vyperTypeSystem vyperTypeCallGraph
  bodyFullCases

Theorem body_return_case_prefix:
  !cx e.
    body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Return (SOME e))
Proof
  rw[body_stmt_prefix_ok_def, gas_shadow_stmt_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_expr_exists_def]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule (Q.SPECL [`cenv`, `cx`, `env`, `e`, `es`, `[]`]
              stmt_expr_body_pre) >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def,
         body_inv_def]
     >- (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
         qexists_tac `cenv` >>
         fs[alloc_limits_stmt_def, alloc_limits_expr_def]) >>
     metis_tac[]) >>
  irule compile_return_some_frag_prefix >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ret_ty`, `es`] mp_tac) >>
  simp[]
QED

Theorem body_return_none_case_prefix:
  !cx. body_stmt_prefix_ok cx (Return NONE)
Proof
  simp[body_stmt_prefix_ok_def, gas_shadow_stmt_def,
       compile_return_none_frag_prefix]
QED

Theorem body_break_case_prefix:
  !cx. body_stmt_prefix_ok cx Break
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_continue_case_prefix:
  !cx. body_stmt_prefix_ok cx Continue
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_raise_bare_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseBare)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED

Theorem body_raise_unreachable_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseUnreachable)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED

Theorem body_pass_case_prefix:
  !cx. body_stmt_prefix_ok cx Pass
Proof
  simp[body_stmt_prefix_ok_def, gas_shadow_stmt_def, compile_pass_frag_prefix]
QED

Theorem body_stmts_nil_case_prefix:
  !cx. body_stmts_prefix_ok cx []
Proof
  simp[body_stmts_prefix_ok_def, stmt_frag_nil_prefix]
QED

Theorem body_expr_stmt_case_prefix:
  !cx e.
    body_expr_full_ok cx e /\
    body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Expr e)
Proof
  rw[body_stmt_prefix_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  qpat_assum `body_inv tops ctx cenv cx`
    (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules
      o MATCH_MP body_inv_contract) >>
  `expr_body_pre cenv cx env e es` by
    (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`, `s` |-> `Expr e`]
       stmtExprAllocationPrePropsTheory.body_inv_stmt_expr_pre_singleton) >>
     simp[supported_stmt_expr_exists_def, int_calls_stmt_def] >>
     disch_then irule >>
     `~is_extcode e` by
       (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
        qexists_tac `cenv` >> fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def]) >>
     mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`, `calls` |-> `[]`]
       stmt_expr_body_pre_main_mods) >>
     gvs[compileUnitTheory.main_module_def, alistTheory.ALOOKUP_def,
         stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def]) >>
  irule compile_expr_stmt_frag_ok_prefix >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`] mp_tac) >>
  simp[]
QED

Theorem body_msg_gas_prefix_case:
  !cx ann args.
    body_expr_prefix_ok cx (Builtin ann (Env MsgGas) args)
Proof
  rw[body_expr_prefix_ok_def] >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[compile_msg_gas_sim_prefix]
QED

Theorem body_expr_prefix_ok_leaf:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_prefix_ok cx e
Proof
  rpt strip_tac >> gvs[body_expr_prefix_ok_def, name_value_prefix, name_vv_prefix,
                       toplevel_name_value_prefix, toplevel_name_vv_prefix,
                       literal_word_value_prefix, literal_vv_prefix] >>
  rw[expr_sim_prefix_def, expr_vv_sim_prefix_def,
     expr_sim_full_pre_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, Once evaluate_def] >>
  PairCases_on `nsid` >>
  simp[lookup_flag_mem_def] >> rpt gen_tac >> rpt BasicProvers.TOP_CASE_TAC >>
  simp[bind_def, read_result_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

val _ = Parse.hide "body";

Theorem body_raise_custom_case_prefix:
  !cx err.
  (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
  (!id positional kwargs tops params es.
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_prefix_ok cx es) ==>
  body_stmt_prefix_ok cx (Raise (RaiseCustomError err))
Proof
  cheat
QED

Theorem body_assert_custom_case_prefix:
  !cx e err.
  (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_full_ok cx es) /\
  (!s tv t id positional kwargs tops params es.
       eval_expr cx e s = (INL tv,t) /\
       err = CustomError id positional kwargs /\
       get_module_code cx (FST id) = SOME tops /\
       lookup_custom_error_args_in (SND id) tops = SOME params /\
       order_custom_error_args params err = SOME es ==>
       body_exprs_prefix_ok cx es) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e (AssertCustomError err))
Proof
  cheat
QED

Theorem body_annassign_case_prefix:
  !cx id typ e.
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_prefix_ok cx e) ==>
  body_stmt_prefix_ok cx (AnnAssign id typ e)
Proof
  cheat
QED

Theorem body_append_case_prefix:
  !cx t e.
  (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
  (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t ==>
  body_stmt_prefix_ok cx (Append t e)
Proof
  cheat
QED

Theorem body_assert_case_prefix:
  !cx e.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e AssertBare)
Proof
  cheat
QED

Theorem body_assert_reason_case_prefix:
  !cx e se.
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_prefix_ok cx se) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e (AssertReason se))
Proof
  cheat
QED

Theorem body_assert_unreachable_case_prefix:
  !cx e.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assert e AssertUnreachable)
Proof
  cheat
QED

Theorem body_assign_case_prefix:
  !cx t e.
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
            struct_args_unique tops) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx t) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assign (BaseTarget t) e)
Proof
  cheat
QED

Theorem body_assign_tuple_case_prefix:
  !cx gs e.
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
  (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_prefix_ok cx (TupleTarget gs) v) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Assign (TupleTarget gs) e)
Proof
  cheat
QED

Theorem body_augassign_case_prefix:
  !cx ty t bop e.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t ==>
  body_stmt_prefix_ok cx (AugAssign ty t bop e)
Proof
  cheat
QED

Theorem env_builtin_expr_prefix_ok:
  !cx ty bt es.
  (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_prefix_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_prefix_ok cx (HD es)) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED

Theorem bop_in_expr_prefix_ok:
  !cx ty bop es.
  (bop = In \/ bop = NotIn) /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty (Bop bop) es)
Proof
  cheat
QED

Theorem bop_expr_prefix_ok:
  !cx ty bop es.
  bop <> In /\
  bop <> NotIn /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty (Bop bop) es)
Proof
  cheat
QED

Theorem make_array_expr_prefix_ok:
  !cx ty bt es.
  (?t n. bt = MakeArray t n) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED

Theorem word_builtin_expr_prefix_ok:
  !cx ty bt es.
  (bt = Not \/ bt = Neg \/ bt = Abs \/ (?d. bt = AsWeiValue d) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED

Theorem precompile_builtin_expr_prefix_ok:
  !cx ty bt es.
  (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED

Theorem body_builtin_case_prefix:
  !cx ty bt es.
  (!s'' x t v code_ty addr tail_s tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) /\
       eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
       body_exprs_full_ok cx [addr]) /\
  (!s'' x t v code_ty addr tail_s tail_vs t'.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) /\
       eval_exprs cx (TL es) tail_s = (INL tail_vs,t') ==>
       body_exprs_prefix_ok cx [addr]) /\
  (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) ==>
       body_exprs_full_ok cx (TL es)) /\
  (!s'' x t v code_ty addr.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = SOME v /\
       v = (code_ty,addr) ==>
       body_exprs_prefix_ok cx (TL es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\
       bt <> Env MsgGas /\ code_slice_source bt es = NONE ==>
       body_exprs_prefix_ok cx es) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) /\
  (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_prefix_ok cx (HD es)) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED

Theorem body_extcall_case_prefix:
  !cx v14 is_static skip_check sig opts es v15.
  (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) es)) /\
  (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_exprs cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_prefix_ok cx (DROP (1 + nargs) es)) /\
  (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_full_ok cx (TAKE nargs (DROP 1 es))) /\
  (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_exprs_prefix_ok cx (TAKE nargs (DROP 1 es))) /\
  body_exprs_full_ok cx (TAKE 1 es) /\
  body_exprs_prefix_ok cx (TAKE 1 es) ==>
  body_expr_prefix_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED

Theorem body_for_case_prefix:
  !cx id typ it n body.
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_prefix_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_prefix_ok cx it) /\
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
       stmt_loop_calls_ok [(NONE,tops)] (For id typ it n body)) ==>
  body_stmt_prefix_ok cx (For id typ it n body)
Proof
  cheat
QED

Theorem body_if_case_prefix:
  !cx e ss1 ss2.
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss1) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_prefix_ok cx ss1) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss2) /\
  (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_prefix_ok cx ss2) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (If e ss1 ss2)
Proof
  cheat
QED

Theorem body_ifexp_case_prefix:
  !cx v5 e1 e2 e3.
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_prefix_ok cx e2) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
  (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_prefix_ok cx e3) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 ==>
  body_expr_prefix_ok cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED

Theorem body_log_case_prefix:
  !cx id es.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_stmt_prefix_ok cx (Log id es)
Proof
  cheat
QED

Theorem body_pop_case_prefix:
  !cx v10 bt.
  body_base_target_full_ok cx bt /\
  body_base_target_prefix_ok cx bt ==>
  body_expr_prefix_ok cx (Pop v10 bt)
Proof
  cheat
QED

Theorem body_raise_reason_case_prefix:
  !cx e.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_stmt_prefix_ok cx (Raise (RaiseReason e))
Proof
  cheat
QED

Theorem body_raw_call_calldata_case_prefix:
  !cx ty flags es v19.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  cheat
QED

Theorem body_raw_call_case_prefix:
  !cx ty flags es v18.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  cheat
QED

Theorem body_raw_log_case_prefix:
  !cx v20 es v21.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call v20 RawLog es v21)
Proof
  cheat
QED

Theorem body_raw_revert_case_prefix:
  !cx v22 es v23.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call v22 RawRevert es v23)
Proof
  cheat
QED

Theorem selfdestruct_expr_prefix:
  !cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann SelfDestructTarget args dflt) es
Proof
  cheat
QED

Theorem body_selfdestruct_case_prefix:
  !cx v24 es v25.
  body_exprs_full_ok cx es /\
  body_exprs_prefix_ok cx es ==>
  body_expr_prefix_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  cheat
QED

Theorem body_stmts_cons_case_prefix:
  !cx s ss.
  (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_full_ok cx ss) /\
  (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_prefix_ok cx ss) /\
  body_stmt_full_ok cx s /\
  body_stmt_prefix_ok cx s ==>
  body_stmts_prefix_ok cx (s::ss)
Proof
  cheat
QED

Theorem body_subscript_case_prefix:
  !cx v8 e1 e2.
  (!s'' res t s'3' res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s'3' = (INL res',t') ==>
       body_expr_full_ok cx e2) /\
  (!s'' res t s'3' res' t'.
       eval_expr cx e1 s'' = (INL res,t) /\
       (if subscript_reads_base cx e1 e2 then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s'3' = (INL res',t') ==>
       body_expr_prefix_ok cx e2) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 ==>
  body_expr_prefix_ok cx (Subscript v8 e1 e2)
Proof
  cheat
QED

Theorem body_type_builtin_case_prefix:
  !cx v11 tb typ es.
  (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (TypeBuiltin v11 tb typ es)
Proof
  cheat
QED

Theorem bytestring_builtin_expr_prefix_ok:
  !cx ty bt es.
    ((?n. bt = CalldataSlice n) \/ (?n. bt = Concat n) \/ (?n. bt = Slice n) \/
     (?n. bt = Uint2Str n)) /\
    (builtin_args_length_ok bt (LENGTH es) ==>
      case code_slice_source bt es of
        NONE => body_exprs_full_ok cx es
      | SOME (code_ty,addr) =>
          body_exprs_full_ok cx (TL es) /\
          (!s tail_vs t. eval_exprs cx (TL es) s = (INL tail_vs,t) ==>
            body_exprs_full_ok cx [addr])) /\
    (builtin_args_length_ok bt (LENGTH es) ==>
      case code_slice_source bt es of
        NONE => body_exprs_prefix_ok cx es
      | SOME (code_ty,addr) =>
          body_exprs_prefix_ok cx (TL es) /\
          (!s tail_vs t. eval_exprs cx (TL es) s = (INL tail_vs,t) ==>
            body_exprs_prefix_ok cx [addr])) ==>
    body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED

Theorem body_intcall_case_prefix:
  !cx v16 src_id_opt fn es v17.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
       ~internal_defaults_msg_gas tops) /\
    (!ts mut nr args dflts ret ss.
       ~MEM (src_id_opt,fn) cx.stk /\
       get_module_code cx src_id_opt = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
       body_stmts_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
       body_exprs_full_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))) /\
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
       body_exprs_full_ok cx es) /\
    (!ts mut nr args dflts ret ss.
       ~MEM (src_id_opt,fn) cx.stk /\
       get_module_code cx src_id_opt = SOME ts /\
       lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,ss) ==>
       body_stmts_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (subst_consts_stmts (module_consts_env (cx_tops cx) []) ss) /\
       body_exprs_prefix_ok (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH dflts - (LENGTH args - LENGTH es))
           (subst_consts_exprs (module_consts_env (cx_tops cx) []) dflts))) /\
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
       body_exprs_prefix_ok cx es) ==>
    body_expr_prefix_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  cheat
QED
