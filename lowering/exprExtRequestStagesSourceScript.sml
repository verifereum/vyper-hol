(* Source-only boundaries for the staged external request operands. *)
Theory exprExtRequestStagesSource
Ancestors
  exprExtRequestShape exprExtRequestUnreadCps exprExtRequestKwargs
  vyperInterpreter vyperState exprSimSource exprSimHypsDefs list rich_list
Libs
  monadsyntax

Theorem extrequest_source_stages:
  eval_expr cx
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::rest) dflt) =
  bind (bind (eval_expr cx addr) (read_result cx)) (\target.
    bind (eval_expr_results cx (TAKE (LENGTH ats) rest)) (\rs.
      bind (eval_exprs cx (DROP (LENGTH ats) rest)) (\kwargs.
        bind (read_results cx rs) (\vs.
          eval_ext_call cx stat skip (fname,ats,rt) opts
            (target::(vs ++ kwargs))))))
Proof
  simp[Once evaluate_def] >>
  simp[Once evaluate_def, bind_assoc, bind_return] >>
  simp[Once evaluate_def, bind_return]
QED

Theorem extrequest_results_preserves_inv:
  !xs es rs ee.
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) xs /\
  expr_sim_inv cenv cx env es /\
  eval_expr_results cx xs es = (INL rs,ee) ==>
  expr_sim_inv cenv cx env ee
Proof
  Induct >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[extrequest_results_cons, bind_def, return_def, AllCaseEqs()] >>
  `expr_body_pre cenv cx env h es` by metis_tac[] >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extrequest_exprs_preserves_inv:
  !xs es vs ee.
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) xs /\
  expr_sim_inv cenv cx env es /\
  eval_exprs cx xs es = (INL vs,ee) ==>
  expr_sim_inv cenv cx env ee
Proof
  Induct >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[extrequest_kwargs_source_cons, bind_def, return_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[] >>
  `expr_body_pre cenv cx env h es` by metis_tac[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extrequest_results_reach_pre:
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) xs /\
  expr_sim_inv cenv cx env es ==>
  !i ee. i < LENGTH xs /\ extrequest_results_reach cx xs es i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee
Proof
  simp[extrequest_results_reach_def] >> rpt strip_tac >>
  `EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) (TAKE i xs)` by
    metis_tac[EVERY_TAKE] >>
  `expr_sim_inv cenv cx env mid` by
    (irule extrequest_results_preserves_inv >> qexistsl [`es with gas_obs := gs`, `rs`, `TAKE i xs`] >> simp[]) >>
  gvs[] >> fs[EVERY_EL] >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem extrequest_kwargs_reach_pre:
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) xs /\
  expr_sim_inv cenv cx env es ==>
  !i ee. i < LENGTH xs /\ extrequest_kwargs_reach cx xs es i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee
Proof
  simp[extrequest_kwargs_reach_def] >> rpt strip_tac >>
  `EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) (TAKE i xs)` by
    metis_tac[EVERY_TAKE] >>
  `expr_sim_inv cenv cx env mid` by
    (irule extrequest_exprs_preserves_inv >> qexistsl [`es with gas_obs := gs`, `vs`, `TAKE i xs`] >> simp[]) >>
  gvs[] >> fs[EVERY_EL] >> first_x_assum (qspec_then `i` mp_tac) >> simp[]
QED

Theorem extrequest_operand_body_pre:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) args d) es ==>
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) args
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  metis_tac[extrequest_body_pre_arg]
QED

(* A successful gas read consumes a real word; the empty case raises. *)
Theorem extrequest_gas_read_replay_probe:
  next_gas_reading (es with gas_obs := gs) = (INL v,ee) ==>
  ?w ws. gs = w::ws /\ v = IntV (&w2n (w:bytes32)) /\
    ee = es with gas_obs := ws /\
    !tail. next_gas_reading (es with gas_obs := [w] ++ tail) =
      (INL v, ee with gas_obs := tail)
Proof
  Cases_on `gs` >> simp[next_gas_reading_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem extrequest_results_counted_cons_probe:
  (!tail. eval_expr cx e (es with gas_obs := used ++ tail) =
    (INL r,mid with gas_obs := tail)) /\
  (!tail. eval_expr_results cx xs (mid with gas_obs := more ++ tail) =
    (INL rs,ee with gas_obs := tail)) ==>
  !tail. eval_expr_results cx (e::xs)
    (es with gas_obs := (used ++ more) ++ tail) =
    (INL (r::rs),ee with gas_obs := tail)
Proof
  rpt strip_tac >>
  qpat_assum `!tail. eval_expr cx e _ = _`
    (qspec_then `more ++ tail` assume_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[extrequest_results_cons, bind_def, return_def, Excl "APPEND_ASSOC"]
QED
