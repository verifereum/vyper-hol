(* Reuse statement admissibility at the reached source write, with the
   observations consumed by the two successful prefixes in source order. *)
Theory bodyPlaceWriteTailAdmissibleMods
Ancestors
  bodyPlacePairedStagesMods stmtSimForRounds gasContext stmtSimDefs
  vyperInterpreter vyperState

(* Beta-reduce the continuation after applying the existing one-cut rule. *)
val reached_bind_tail = SRULE [gas_admissible_gas_obs] gas_admissible_bind_tail;

Theorem assign_reached_write_admissible_mods:
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
  (!tail. eval_target_place cx bt (mid with gas_obs := ys ++ tail) =
          (INL p,ee with gas_obs := tail)) ==>
  gas_admissible (write_place cx p v) (stmt_res_ok lctx) ee
Proof
  `eval_stmt cx (Assign (BaseTarget bt) e) =
   bind (bind (eval_expr cx e) (read_result cx))
        (\v. bind (eval_target_place cx bt) (\p. write_place cx p v))` by
    simp[Once evaluate_def, bind_assoc] >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all_then (assume_tac o BETA_RULE) reached_bind_tail >>
  drule_all_then (ACCEPT_TAC o BETA_RULE) reached_bind_tail
QED

Theorem append_reached_append_admissible_mods:
  gas_admissible (eval_stmt cx (Append bt e)) (stmt_res_ok lctx) es /\
  (!tail. eval_target_place cx bt (es with gas_obs := xs ++ tail) =
          (INL p,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e) (read_result cx) (mid with gas_obs := ys ++ tail) =
          (INL v,ee with gas_obs := tail)) ==>
  gas_admissible (append_place cx p v) (stmt_res_ok lctx) ee
Proof
  rewrite_tac[append_source_stages_mods] >> strip_tac >>
  drule_all_then (assume_tac o BETA_RULE) reached_bind_tail >>
  drule_all_then (ACCEPT_TAC o BETA_RULE) reached_bind_tail
QED
