Theory callCodeEval
Ancestors
  callCodeEvalPrims callCodeEvalSlice callCodeEvalInternal supportedStmtTraverse
  vyperInterpreter vyperContext vyperState vyperAST vyperCreate exprLowering list sorting
  supportedExprTraverse finite_map
Libs
  monadsyntax

(* Compare continuations only in states reached by the common prefix. *)
Theorem call_code_bind_eq[local]:
  (bind f g s = bind f h s <=> !x t. f s = (INL x,t) ==> g x t = h x t) /\
  (ignore_bind f k s = ignore_bind f l s <=> !x t. f s = (INL x,t) ==> k t = l t)
Proof
  Cases_on `f s` >> Cases_on `q` >> simp[bind_def, ignore_bind_def]
QED

Theorem call_code_create_updates[local]:
  (blueprint_literal_offset (cx with txn := cx.txn with code := c) salt es =
   blueprint_literal_offset cx salt es) /\
  (eval_create_operands (cx with txn := cx.txn with code := c)
     kind salt rof ts literal_offset vs =
   eval_create_operands cx kind salt rof ts literal_offset vs)
Proof
  conj_tac
  >- simp[oneline blueprint_literal_offset_def, call_code_primitive_updates] >>
  Cases_on `kind` >> simp[eval_create_operands_def, call_code_primitive_updates]
QED

Theorem no_self_code_create_order[local]:
  ~supported_exprs_exists is_self_code es ==>
  ~supported_exprs_exists is_self_code (create_operand_order kind salt es)
Proof
  strip_tac >> fs[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS] >>
  Cases_on `kind` >> Cases_on `es` >>
  gvs[create_operand_order_def, rich_listTheory.EVERY_TAKE,
      rich_listTheory.EVERY_DROP] >>
  rename1 `create_operand_order RawCreate _ (operand :: rest)` >>
  Cases_on `rest` >>
  gvs[create_operand_order_def, rich_listTheory.EVERY_TAKE,
      rich_listTheory.EVERY_DROP]
QED

(* Keep the callable closure atomic in ordinary recursive cases; unfold it
   only for the context obtained by pushing an internal-call frame. *)
Theorem evaluate_no_self_code_update_aux[local]:
  (!cx. closed cx <=>
    !src ts fn mut nr args ds rt b.
      get_module_code cx src = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,ds,rt,b) ==>
      ~supported_exprs_exists is_self_code ds /\ ~supported_stmts_expr_exists is_self_code b) ==>
  (!cx s c. closed cx /\ ~supported_stmt_expr_exists is_self_code s ==>
     eval_stmt (cx with txn := cx.txn with code := c) s = eval_stmt cx s) /\
  (!cx ss c. closed cx /\ ~supported_stmts_expr_exists is_self_code ss ==>
     eval_stmts (cx with txn := cx.txn with code := c) ss = eval_stmts cx ss) /\
  (!cx it c. closed cx /\ ~supported_iterator_exists is_self_code it ==>
     eval_iterator (cx with txn := cx.txn with code := c) it = eval_iterator cx it) /\
  (!cx ty nm body rs c. closed cx /\ ~supported_stmts_expr_exists is_self_code body ==>
     eval_for (cx with txn := cx.txn with code := c) ty nm body rs = eval_for cx ty nm body rs) /\
  (!cx e c. closed cx /\ ~supported_expr_exists is_self_code e ==>
     eval_expr (cx with txn := cx.txn with code := c) e = eval_expr cx e) /\
  (!cx es c. closed cx /\ ~supported_exprs_exists is_self_code es ==>
     eval_exprs (cx with txn := cx.txn with code := c) es = eval_exprs cx es) /\
  (!cx t c. closed cx /\ ~supported_target_exists is_self_code t ==>
     eval_base_place (cx with txn := cx.txn with code := c) t = eval_base_place cx t) /\
  (!cx t c. closed cx /\ ~supported_target_exists is_self_code t ==>
     eval_target_place (cx with txn := cx.txn with code := c) t = eval_target_place cx t) /\
  (!cx g v c. closed cx /\ ~supported_assignment_exists is_self_code g ==>
     assign_tuple_targets (cx with txn := cx.txn with code := c) g v = assign_tuple_targets cx g v) /\
  (!cx gs vs c. closed cx /\ ~supported_assignments_exists is_self_code gs ==>
     assign_tuple_target_list (cx with txn := cx.txn with code := c) gs vs =
       assign_tuple_target_list cx gs vs)
Proof
  disch_then (mk_asm "closure") >>
  ho_match_mp_tac evaluate_ind >>
  simp[supported_expr_exists_def, supported_stmt_expr_exists_def,
       supported_iterator_exists_def, supported_assignment_exists_def,
       supported_raise_exists_def, supported_assert_exists_def] >>
  rpt strip_tac
  >>~- ([`eval_expr _ (Call _ (IntCall _) _ _) = _`], suspend "internal")
  >>~- ([`eval_stmt _ (Raise (RaiseCustomError err)) = _`], suspend "custom_raise")
  >>~- ([`eval_stmt _ (Assert _ (AssertCustomError err)) = _`], suspend "custom_assert")
  >>~- ([`eval_expr _ (Call _ (CreateTarget _ _ _ _) _ _) = _`], suspend "create")
  >>~- ([`eval_expr _ (Builtin _ _ _) = _`], suspend "builtin") >>
  PURE_ONCE_REWRITE_TAC [evaluate_def] >>
  gvs[call_code_primitive_updates, no_self_code_operands] >>
  simp[FUN_EQ_THM, Cong bind_cong, Cong ignore_bind_cong, Cong finally_cong,
       Cong try_cong, SF SFY_ss] >>
  suspend "remaining"
QED

Resume evaluate_no_self_code_update_aux[custom_raise]:
  PURE_ONCE_REWRITE_TAC [evaluate_def] >>
  Cases_on `err` >> gvs[call_code_primitive_updates] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[supported_exprs_exists_every] >>
  drule_then mp_tac (cj 4 no_self_code_operands) >>
  simp[supported_exprs_exists_every]
QED

Resume evaluate_no_self_code_update_aux[internal]:
  irule eval_internal_call_code_update_step >>
  simp[call_code_primitive_updates, Excl "lock_if_nr_def"] >>
  gvs[type_check_def, assert_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs(),
      push_function_def, get_scopes_def, set_scopes_def] >>
  map_every qx_gen_tac [`ts`,`mut`,`nr`,`args`,`ds`,`ret`,`body'`] >> strip_tac >>
  `closed (cx with stk updated_by CONS (src_id_opt,fn))` by
    (asm "closure" (qspec_then `cx with stk updated_by CONS (src_id_opt,fn)` mp_tac) >>
     asm "closure" (qspec_then `cx` mp_tac) >> simp[get_module_code_def] >> metis_tac[get_module_code_def]) >>
  `~supported_exprs_exists is_self_code ds /\ ~supported_stmts_expr_exists is_self_code body'` by
    (asm "closure" (qspec_then `cx` mp_tac) >> simp[] >>
     disch_then drule_all >> simp[]) >>
  map_every qx_gen_tac [`vs`,`s`,`t`] >> strip_tac >>
  conj_tac >-
    (qpat_x_assum `!ts tup s vs t. _`
       (qspecl_then [`ts`,`(mut,nr,args,ds,ret,body')`,`s`,`vs`,`t`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM, no_self_code_operands]) >>
  map_every qx_gen_tac [`prev`,`dvals`,`sd`,`td`,`env`,`rtv`,`sl`,`tl`] >> strip_tac >>
  qpat_x_assum `!ts tup s vs t sp sd dv td env rtv sl tl. _`
    (qspecl_then [`ts`,`(mut,nr,args,ds,ret,body')`,`s`,`vs`,`t`,
                  `sd with scopes := prev`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >>
  disch_then drule_all >> simp[]
QED

Resume evaluate_no_self_code_update_aux[custom_assert]:
  PURE_ONCE_REWRITE_TAC [evaluate_def] >>
  gvs[call_code_primitive_updates] >>
  simp[FUN_EQ_THM, call_code_bind_eq, switch_BoolV_def] >>
  rpt strip_tac >> Cases_on `err` >> gvs[] >>
  Cases_on `get_module_code cx (FST p)` >> gvs[] >>
  rename1 `get_module_code cx (FST p) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops` >> gvs[] >>
  rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)` >>
  gvs[supported_exprs_exists_every] >>
  drule_then mp_tac (cj 4 no_self_code_operands) >>
  simp[supported_exprs_exists_every] >> strip_tac >>
  qpat_x_assum `!s tv t. eval_expr _ _ s = _ ==> _` drule >> simp[]
QED

Resume evaluate_no_self_code_update_aux[create]:
  PURE_ONCE_REWRITE_TAC [evaluate_def] >>
  simp[call_code_create_updates] >>
  qpat_x_assum `!c. closed cx /\ _ ==> _` (qspec_then `c` mp_tac) >>
  impl_tac >- simp[no_self_code_create_order] >>
  disch_then SUBST1_TAC >> simp[]
QED

Resume evaluate_no_self_code_update_aux[remaining]:
  markerLib.RESUME_TAC >>
  rpt (CHANGED_TAC (simp[call_code_bind_eq, switch_BoolV_def,
                        call_code_primitive_updates] >> rpt strip_tac)) >>
  rpt (first_x_assum (drule_all_then assume_tac) >>
       rpt (CHANGED_TAC (simp[call_code_bind_eq] >> rpt strip_tac)))
  >>> SELECT_LT_THEN
    (qpat_assum `!vs. v = ArrayV (TupleV vs) ==> _`
       (K (Cases_on `v` >> gvs[])))
    (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  Cases_on `broke` >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume evaluate_no_self_code_update_aux[builtin]:
  PURE_ONCE_REWRITE_TAC [evaluate_def] >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)` >>
  gvs[call_code_primitive_updates, type_check_def,
      vyperStateTheory.assert_def, return_def, raise_def] >>
  simp[FUN_EQ_THM, ignore_bind_apply, vyperStateTheory.assert_def,
       return_def, raise_def] >>
  Cases_on `bt = Len` >-
    (Cases_on `es` >> gvs[builtin_args_length_ok_def, supported_exprs_exists_every]) >>
  Cases_on `bt = Env MsgGas` >> gvs[] >>
  Cases_on `code_slice_source bt es` >> gvs[] >>
  rename1 `code_slice_source bt es = SOME p` >> PairCases_on `p` >>
  drule_all_then strip_assume_tac no_self_code_slice_operands >>
  gvs[evaluate_code_source_def, call_code_primitive_updates,
      supported_exprs_exists_every] >>
  gen_tac >> AP_THM_TAC >> BINOP_TAC >> simp[] >>
  BINOP_TAC >> simp[] >>
  simp[FUN_EQ_THM, call_code_bind_eq] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >> simp[]
QED

Finalise evaluate_no_self_code_update_aux


Theorem evaluate_no_self_code_update:
  (!src tops fn mut nr args ds rt body.
    get_module_code cx src = SOME tops /\
    lookup_callable_function cx.in_deploy fn tops = SOME (mut,nr,args,ds,rt,body) ==>
    ~supported_exprs_exists is_self_code ds /\
    ~supported_stmts_expr_exists is_self_code body) ==>
  (!ds. ~supported_exprs_exists is_self_code ds ==>
        eval_exprs (cx with txn := cx.txn with code := c) ds = eval_exprs cx ds) /\
  (!ss. ~supported_stmts_expr_exists is_self_code ss ==>
        eval_stmts (cx with txn := cx.txn with code := c) ss = eval_stmts cx ss)
Proof
  qspec_then `\cx. !src tops fn mut nr args ds rt body.
    get_module_code cx src = SOME tops /\
    lookup_callable_function cx.in_deploy fn tops = SOME (mut,nr,args,ds,rt,body) ==>
    ~supported_exprs_exists is_self_code ds /\
    ~supported_stmts_expr_exists is_self_code body`
    mp_tac (GEN_ALL evaluate_no_self_code_update_aux) >>
  simp[] >> metis_tac[]
QED
