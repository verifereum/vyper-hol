(* Source-only bridges for counted mixed word/vv operand composition. *)
Theory exprSimBopRestWordCompose
Ancestors
  gasSummary gasSummaryCompose gasExemptCert exprBopSimProps vyperState
  vyperInterpreter exprSimMemorySource

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
