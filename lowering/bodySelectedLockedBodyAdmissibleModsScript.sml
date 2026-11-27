(* Admissibility at the reached lock-success state of a qualified call. *)
Theory bodySelectedLockedBodyAdmissibleMods
Ancestors
  linkedBodyLoopCalls vyperTypeCallStackSoundness vyperInterpreter
  vyperState gasContext exprSimDefs stmtSimDefs nonreentrantEquiv
Libs
  monadsyntax

val pushed = ``cx with stk updated_by CONS (src,name)``;
val rest = ``do lock_if_nr cx nr (is_view_mut mut);
  rv <- finally_unless_halt
    (finally
       (try (do eval_stmts (^pushed) ss; return NoneV od) handle_function)
       (pop_function prev))
    (unlock_if_nr cx nr (is_view_mut mut));
  crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
  return (Value crv)
  od``;

(* The handler catches returns, but maps escaped loop control to a TypeError.
   Cleanup preserves that error, so the admissible continuation excludes it.
   Constant substitution is needed only to transport the call keys. *)
Theorem selected_locked_body_admissible_mods:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  call_evaluation_safe cx ((src,name)::calls) /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  (!gs. lock_if_nr cx nr (is_view_mut mut) (es1 with gas_obs := gs) =
          (INL (),locked with gas_obs := gs)) /\
  gas_admissible (^rest) expr_vv_res_ok es1 ==>
  call_evaluation_safe (^pushed)
    (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
  gas_admissible (eval_stmts (^pushed) ss) (stmt_res_ok NoLoop) locked
Proof
  strip_tac >> conj_tac
  >- (drule_then strip_assume_tac checked_subst_consts_int_calls_mods >>
      simp[] >>
      drule_all_then ACCEPT_TAC
        (SIMP_RULE bool_ss []
           (Q.INST [`callee` |-> `(src,fn)`] call_evaluation_safe_push_body))) >>
  rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _`
    (mp_tac o Q.SPEC `gs` o REWRITE_RULE [gas_admissible_def]) >>
  pure_rewrite_tac[ignore_bind_def, bind_def] >>
  asm_simp_tac bool_ss [] >>
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> simp[stmt_res_ok_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[stmt_res_ok_def, try_def, handle_function_def, finally_def,
       finally_unless_halt_def, ignore_bind_def, bind_def,
       pop_function_def, set_scopes_def, return_def, raise_def,
       unlock_if_nr_def, release_nonreentrant_lock_execution,
       COND_RATOR, vyperMiscTheory.option_CASE_rator] >>
  Cases_on `nr /\ mut <> View /\ mut <> Pure` >>
  Cases_on `cx.nonreentrant_slot` >> fs[expr_vv_res_ok_def]
QED
