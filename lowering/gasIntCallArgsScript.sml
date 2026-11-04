(* Actual internal-call args exception transport. *)
Theory gasIntCallArgs
Ancestors
  gasExemptCert gasSummary gasSummaryCompose fragGasFocus
  vyperCall vyperState vyperInterpreter vyperContext vyperValue vyperAST
  venomState list
Libs
  monadsyntax

Theorem gas_exempt_intcall_args:
  !memory tops ctx func cx ty src fn args drv es s0 marks err ee leaf finish
   ts mut params ret body.
    ~MEM (src, fn) cx.stk /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut, F, params, [], ret, body) /\
    LENGTH args = LENGTH params /\
    gas_exempt_cert memory tops (ctx, func)
      (ignore_bind
        (bind (eval_expr_results cx args) (read_results cx)) (return ()))
      (es, s0) marks (err, ee) (leaf, finish) ==>
    gas_exempt_cert memory tops (ctx, func)
      (ignore_bind (eval_expr cx (Call ty (IntCall (src, fn)) args drv))
        (return ()))
      (es, s0) marks (err, ee) (leaf, finish)
Proof
  rpt strip_tac >>
  drule_all eval_expr_intcall_args_factor >>
  disch_then (qspecl_then [`ty`, `drv`] SUBST1_TAC) >>
  qmatch_goalsub_abbrev_tac `ignore_bind (bind a k) (return ())` >>
  `ignore_bind (bind a k) (return ()) =
   bind a (\v. ignore_bind (k v) (return ()))` by
    (simp[FUN_EQ_THM, ignore_bind_def] >> gen_tac >>
     Cases_on `a x` >> Cases_on `q` >> simp[bind_def]) >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_values >>
  simp[Abbr `a`, SF ETA_ss]
QED

(* Check the frozen root's full proof ancestry, not only its final tactic. *)
