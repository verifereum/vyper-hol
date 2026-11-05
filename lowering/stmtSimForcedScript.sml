(* A statement that forces one expression and then runs a source
   continuation that reads no gas, while the target runs a GAS-free
   suffix: the expression's counted outcome lifts to the statement's.
   The suffix's zero marks keep the expression's own marks for the
   whole statement, and an exemption of the expression stays one of the
   statement. *)
Theory stmtSimForced
Ancestors
  stmtSimDefs exprSimDefs gasOutcome gasSummary gasSummaryCompose
  gasExemptCert gasContext fragGasMode fragExec
  vyperInterpreter vyperState vyperExprNoControl list
Libs
  monadsyntax

Theorem ignore_bind_bind_value[local]:
  !(a : evaluation_state -> value evaluation_result) k.
    ignore_bind (bind a k) (return ()) =
    bind a (\v. ignore_bind (k v) (return ()))
Proof
  simp[ignore_bind_def, FUN_EQ_THM, bind_def] >> rpt gen_tac >>
  Cases_on `a x` >> Cases_on `q` >> simp[]
QED

Theorem expr_exit_INR_unit[local]:
  !ex r. expr_exit (INR ex : unit + exception) r <=>
         expr_exit (INR ex : value + exception) r
Proof
  Cases_on `r` >> Cases_on `ex` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

(* The source continuation of a forced value runs from the expression's
   end state, and the target suffix from the expression's end, with no
   gas reading on either side. *)
Theorem forced_then_summary:
  !memory ctx func cx e k marks es s0 P Q R.
    gas_summary_at memory (ctx, func) marks
      (bind (eval_expr cx e) (read_result cx)) (es, s0)
      (\res ee t. ?v. res = INL v /\ P v ee t)
      (\res ee r. expr_exit res r) /\
    (!v ee t.
       P v ee t /\
       (?gs ee1. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
                 (INL v, ee1)) ==>
       ?res ee' r.
         (!tail. k v (ee with gas_obs := tail) =
                 (res, ee' with gas_obs := tail)) /\
         gas_marked_path memory ctx func t 0 r /\
         ((?t'. r = OK t' /\ Q res (ee' with gas_obs := []) t') \/
          (exit_result r /\ R res (ee' with gas_obs := []) r))) /\
    (!ex ee r. expr_exit (INR ex : value + exception) r ==>
               R (INR ex) ee r) ==>
    gas_summary_at memory (ctx, func) marks
      (bind (bind (eval_expr cx e) (read_result cx)) k) (es, s0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- (gvs[] >>
      `?gs ee1. bind (eval_expr cx e) (read_result cx)
                  (es with gas_obs := gs) = (INL v, ee1)` by
        (fs[gas_marked_exec_def] >> metis_tac[]) >>
      first_x_assum (qspecl_then [`v`, `es_end with gas_obs := []`, `t`]
        mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      rename1 `gas_marked_path memory ctx func t 0 r'` >>
      `gas_marked_exec memory (ctx,func) (k v) (es_end with gas_obs := [], t)
         [] res ee' r'` by fs[gas_marked_exec_def] >>
      `gas_marked_exec memory (ctx,func)
         (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0)
         (marks ++ []) res ee' r'` by
        (irule gas_marked_exec_bind_normal >> metis_tac[]) >>
      qexistsl_tac [`res`, `ee'`, `r'`] >> fs[]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem forced_then_outcome:
  !memory tops ctx func cx e k es s0 P Q R.
    gas_outcome memory tops (ctx, func)
      (bind (eval_expr cx e) (read_result cx)) (es, s0)
      (\res ee t. ?v. res = INL v /\ P v ee t)
      (\res ee r. expr_exit res r) /\
    (!v ee t.
       P v ee t /\
       (?gs ee1. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
                 (INL v, ee1)) ==>
       ?res ee' r.
         (!tail. k v (ee with gas_obs := tail) =
                 (res, ee' with gas_obs := tail)) /\
         gas_marked_path memory ctx func t 0 r /\
         ((?t'. r = OK t' /\ Q res (ee' with gas_obs := []) t') \/
          (exit_result r /\ R res (ee' with gas_obs := []) r))) /\
    (!ex ee r. expr_exit (INR ex : value + exception) r ==>
               R (INR ex) ee r) ==>
    gas_outcome memory tops (ctx, func)
      (bind (bind (eval_expr cx e) (read_result cx)) k) (es, s0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule forced_then_summary >> conj_tac >- first_assum ACCEPT_TAC >>
      qexists_tac `P` >> conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  ONCE_REWRITE_TAC [ignore_bind_bind_value] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

(* An admissible statement that forces e first leaves e's forced value
   only expression results: e raises no control exception. *)
Theorem forced_then_admissible:
  !cx e (k : value -> evaluation_state -> unit evaluation_result) lctx es.
    gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) k)
      (stmt_res_ok lctx) es ==>
    gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rpt gen_tac >> strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `bind (bind (eval_expr cx e) (read_result cx)) k (es with gas_obs := gs) =
     (INR ex, ee)` by simp[Once bind_def] >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

(* The statement form: stmt_framed_frag's obligation for a statement
   whose source action forces e and then continues without gas. *)
Theorem forced_then_stmt_outcome:
  !ctx func cx lctx RetQ cenv cenv' sa sb s0 s e k es P.
    eval_stmt cx s = bind (bind (eval_expr cx e) (read_result cx)) k /\
    gas_outcome F (cx_tops cx) (ctx, func)
      (bind (eval_expr cx e) (read_result cx)) (es, s0)
      (\res ee t. ?v. res = INL v /\ P v ee t)
      (\res ee r. expr_exit res r) /\
    (!v ee t.
       P v ee t /\
       (?gs ee1. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
                 (INL v, ee1)) ==>
       ?res ee' r.
         (!tail. k v (ee with gas_obs := tail) =
                 (res, ee' with gas_obs := tail)) /\
         gas_marked_path F ctx func t 0 r /\
         ((?t'. r = OK t' /\
                stmt_post ctx func cx lctx cenv cenv' sa sb s0 res
                  (ee' with gas_obs := []) t') \/
          (exit_result r /\
           !tail. stmt_exit RetQ (ee' with gas_obs := tail) res r))) ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_stmt cx s) (es, s0)
      (stmt_post ctx func cx lctx cenv cenv' sa sb s0)
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ = _` SUBST1_TAC >>
  irule forced_then_outcome >> conj_tac
  >- simp[stmt_exit_def, expr_exit_INR_unit] >>
  qexists_tac `P` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >>
  disch_then (fn th => first_x_assum (fn h => mp_tac (MATCH_MP h th))) >>
  simp[]
QED
