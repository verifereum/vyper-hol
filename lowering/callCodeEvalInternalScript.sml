Theory callCodeEvalInternal
Ancestors
  vyperInterpreter vyperContext vyperState finite_map
Libs
  monadsyntax

Theorem internal_call_lock_code_update[local]:
  lock_if_nr (cx with txn := (cx.txn with code := c)) nr view =
  lock_if_nr cx nr view /\
  unlock_if_nr (cx with txn := (cx.txn with code := c)) nr view =
  unlock_if_nr cx nr view
Proof
  simp[lock_if_nr_def, unlock_if_nr_def, check_not_static_def]
QED

Theorem internal_call_push_bind[local]:
  bind (push_function p env cx) k =
  ignore_bind (set_scopes [env]) (k (cx with stk updated_by CONS p))
Proof
  simp[FUN_EQ_THM, bind_def, ignore_bind_def, return_def, push_function_def,
       set_scopes_def]
QED

(* The three equalities are required only after the successful prefixes of
   the respective recursive calls in evaluate_ind. *)
Theorem eval_internal_call_code_update_step:
  get_module_code (cx with txn := (cx.txn with code := c)) sid =
    get_module_code cx sid /\
  get_tenv (cx with txn := (cx.txn with code := c)) = get_tenv cx /\
  (!ts mut nr args ds ret body.
    ~MEM (sid,fn) cx.stk /\
    get_module_code cx sid = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,ds,ret,body) /\
    LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH ds ==>
    !cxd cxd' defaults.
      cxd = (cx with stk updated_by CONS (sid,fn)) /\
      cxd' = (cxd with txn := (cxd.txn with code := c)) /\
      defaults = DROP (LENGTH ds - (LENGTH args - LENGTH es)) ds ==>
      eval_exprs (cx with txn := (cx.txn with code := c)) es = eval_exprs cx es /\
      (!vs s t. eval_exprs cx es s = (INL vs,t) ==>
        eval_exprs cxd' defaults = eval_exprs cxd defaults /\
        (!prev dvals sd td env rtv sl tl.
          finally (do set_scopes [FEMPTY]; eval_exprs cxd defaults od)
            (set_scopes prev) sd = (INL dvals,td) /\
          bind_arguments (get_tenv cx) args (vs ++ dvals) = SOME env /\
          evaluate_type (get_tenv cx) ret = SOME rtv /\
          lock_if_nr cx nr (is_view_mut mut) sl = (INL (),tl) ==>
          eval_stmts cxd' body = eval_stmts cxd body))) ==>
  eval_expr (cx with txn := (cx.txn with code := c)) (Call ty (IntCall (sid,fn)) es d) =
  eval_expr cx (Call ty (IntCall (sid,fn)) es d)
Proof
  simp_tac bool_ss [] >>
  strip_tac >>
  PURE_ONCE_REWRITE_TAC [evaluate_def] >>
  rewrite_tac [internal_call_lock_code_update, internal_call_push_bind] >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", LET_THM] >>
  irule ignore_bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  `~MEM (sid,fn) cx.stk` by
    (qpat_x_assum `type_check _ _ _ = _` mp_tac >>
     simp[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]) >>
  AP_THM_TAC >> irule bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  rename1 `lift_option_type (get_module_code cx sid) _ _ = (INL ts,_)` >>
  `get_module_code cx sid = SOME ts` by
    (qpat_x_assum `lift_option_type _ _ _ = (INL ts,_)` mp_tac >>
     simp[lift_option_type_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  AP_THM_TAC >> irule bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  rename1 `lift_option_type (lookup_callable_function _ _ _) _ _ = (INL tup,_)` >>
  `lookup_callable_function cx.in_deploy fn ts = SOME tup` by
    (qpat_x_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _` mp_tac >>
     simp[lift_option_type_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  PairCases_on `tup` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  AP_THM_TAC >> irule ignore_bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  `LENGTH es <= LENGTH tup2 /\ LENGTH tup2 - LENGTH es <= LENGTH tup3` by
    (qpat_x_assum `type_check _ "IntCall args length" _ = _` mp_tac >>
     simp[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]) >>
  qpat_x_assum `!ts mut nr args ds ret body. _` (drule_all_then mp_tac) >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def"] >>
  strip_tac >>
  AP_THM_TAC >> irule bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!vs s t. eval_exprs cx es s = _ ==> _`
    (drule_then strip_assume_tac) >>
  AP_THM_TAC >> irule bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  AP_THM_TAC >> irule bind_cong_implicit >> asm_simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  AP_THM_TAC >> irule bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  AP_THM_TAC >> irule bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  AP_THM_TAC >> irule ignore_bind_cong_implicit >> simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lift_option_type (bind_arguments _ _ _) _ _ = _`
    (strip_assume_tac o SRULE [lift_option_type_def, vyperMiscTheory.option_CASE_rator,
                             return_def, raise_def, AllCaseEqs()]) >>
  qpat_x_assum `lift_option_type (evaluate_type _ _) _ _ = _`
    (strip_assume_tac o SRULE [lift_option_type_def, vyperMiscTheory.option_CASE_rator,
                             return_def, raise_def, AllCaseEqs()]) >>
  rename1 `lock_if_nr _ _ _ _ = (INL locked,_)` >> Cases_on `locked` >>
  qpat_x_assum `!prev dvals sd td env rtv sl tl. _` (drule_all_then assume_tac) >>
  asm_rewrite_tac []
QED
