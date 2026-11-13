(* Caller-general source preparation.  No staging implementation or sibling
   seam is used here.  Keep the acquisition before push on failure paths. *)
Theory bodyIntCallSeamGeneralPrefix
Ancestors
  bodyIntCallSeamDefs intCallStep aggregateCountedOutcome vyperInterpreter vyperState
Libs
  monadsyntax

Theorem intcall_defaults_source_factor:
  ~MEM (src,name) cx.stk /\ get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts ==>
  eval_expr cx (Call ann (IntCall (src,name)) es dflt) =
  (do vs <- eval_exprs cx es;
      prev <- get_scopes;
      dvs <- finally
        (do set_scopes [FEMPTY];
            eval_exprs (cx with stk updated_by CONS (src,name))
              (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) od)
        (set_scopes prev);
      penv <- lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dvs))
        "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret) "IntCall eval ret";
      lock_if_nr cx nr (is_view_mut mut);
      cxf <- push_function (src,name) penv cx;
      rv <- finally_unless_halt
        (finally (try (do eval_stmts cxf ss; return NoneV od) handle_function)
          (pop_function prev))
        (unlock_if_nr cx nr (is_view_mut mut));
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv) od)
Proof
  strip_tac >> simp[Once evaluate_def, type_check_def, assert_def,
    lift_option_type_def, bind_apply, ignore_bind_apply, return_def, FUN_EQ_THM]
QED

(* This conditional commutation deliberately says nothing about failed locks:
   their source exit still has the caller's scopes, not the callee's. *)
Theorem intcall_lock_push_success:
  lock_if_nr cx nr view s = (INL (),u) ==>
  (do lock_if_nr cx nr view;
      cxf <- push_function nsid penv cx; k cxf od) s =
  (do lock_if_nr cx nr view;
      k (cx with stk updated_by CONS nsid) od) (s with scopes := [penv])
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  simp[acquire_nonreentrant_lock_def, ignore_bind_def, bind_def,
    get_transient_storage_def, update_transient_def, return_def,
    raise_def, check_not_static_def, check_def, assert_def, COND_RATOR] >>
  rpt IF_CASES_TAC >>
  simp[bind_def, return_def, raise_def, update_transient_def, assert_def,
       push_function_def] >>
  Cases_on `view` >> simp[push_function_def, bind_def, return_def]
QED

Theorem intcall_source_success_rest:
  ~MEM (NONE,name) cx.stk /\ get_module_code cx NONE = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts /\
  eval_exprs cx es s = (INL vs,t1) /\
  eval_exprs (cx with stk updated_by CONS (NONE,name))
    (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
    (t1 with scopes := [FEMPTY]) = (INL dvs,td) /\
  bind_arguments (get_tenv cx) args (vs ++ dvs) = SOME penv /\
  evaluate_type (get_tenv cx) ret = SOME rtv /\
  lock_if_nr cx nr (is_view_mut mut) (td with scopes := t1.scopes) = (INL (),u) ==>
  eval_expr cx (Call ann (IntCall (NONE,name)) es dflt) s =
  intcall_rest cx name mut nr ss t1.scopes rtv (td with scopes := [penv])
Proof
  strip_tac >> drule_all intcall_defaults_source_factor >>
  disch_then (qspecl_then [`dflt`, `ann`] SUBST1_TAC) >>
  asm_simp_tac (srw_ss()) [bind_apply, ignore_bind_apply, get_scopes_def,
       return_def, finally_def, set_scopes_def, lift_option_type_def,
       Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  rewrite_tac[intcall_rest_def] >>
  drule intcall_lock_push_success >>
  disch_then (qspecl_then [`penv`, `(NONE,name)`] mp_tac) >>
  asm_simp_tac (srw_ss()) [bind_apply, ignore_bind_apply, push_function_def,
    return_def, lift_option_type_def, Excl "lock_if_nr_def", Excl "unlock_if_nr_def",
    Excl "is_view_mut_def"] >>
  disch_then (qspec_then `\c. return ARB` mp_tac) >>
  namedCases_on `lock_if_nr cx nr (is_view_mut mut) (td with scopes := [penv])`
    ["res mid"] >>
  Cases_on `res` >> simp[return_def] >> strip_tac >> gvs[]
QED
