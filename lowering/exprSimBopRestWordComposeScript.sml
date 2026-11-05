(* Source-only bridges for counted mixed word/vv operand composition. *)
Theory exprSimBopRestWordCompose
Ancestors
  gasSummary gasSummaryCompose gasExemptCert exprBopSimProps vyperState
  vyperInterpreter exprSimMemorySource list

Theorem rest_word_marked_read:
  gas_marked_exec memory (ctx, func) (eval_expr cx e)
    (es,s0) marks (INL tv) mid (OK t) /\
  (!tail. read_result cx tv (mid with gas_obs := tail) =
    (INL v, mid with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx, func)
    (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) mid (OK t)
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  simp[bind_def]
QED

Theorem rest_word_raw_second_exempt_cert:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx e2) (return ()))
    (mid with gas_obs := [],t) right (err,ee) (leaf,sf) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2]))
                      (read_result cx)) (return ()))
    (es,s0) (left ++ right) (err,ee) (leaf,sf)
Proof
  strip_tac >> drule force_exempt_cert >> strip_tac >>
  irule (REWRITE_RULE [ETA_AX] bop_second_exempt_cert) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_mixed_marked_tail:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e2)
    (mid with gas_obs := [],t) right (INL tv2) fin (OK u) /\
  (!tail. read_result cx tv2 (fin with gas_obs := tail) =
    (INL v2,fin with gas_obs := tail)) /\
  gas_marked_exec memory (ctx,func)
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin with gas_obs := [],u) suffix res last r ==>
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0) (left ++ right ++ suffix) res last r
Proof
  strip_tac >> drule_all rest_word_marked_read >> strip_tac >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_mixed_tail_summary:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e2)
    (mid with gas_obs := [],t) right (INL tv2) fin (OK u) /\
  (!tail. read_result cx tv2 (fin with gas_obs := tail) =
    (INL v2,fin with gas_obs := tail)) /\
  gas_marked_exec memory (ctx,func)
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin with gas_obs := [],u) suffix res last r /\
  ((?z. r = OK z /\ Q res (last with gas_obs := []) z) \/
   (exit_result r /\ R res (last with gas_obs := []) r)) ==>
  gas_summary_at memory (ctx,func) (left ++ right ++ suffix)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0) Q R
Proof
  strip_tac >> drule_all rest_word_mixed_marked_tail >> strip_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `last`, `r`] >> simp[]
QED
