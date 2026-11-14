Theory assignPlaceEmpty
Ancestors
  immutableAssignEmpty vyperInterpreter vyperState exprSimHypsDefs
Libs monadsyntax

(* The shortcut skips RHS code, but not the target's gas observations. *)
Theorem assign_place_empty_source_action:
  expr_body_pre cenv cx env e es /\ is_empty_value_expr e /\
  has_length_word (expr_type e) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv ==>
  !tail. eval_stmt cx (Assign (BaseTarget bt) e) (es with gas_obs := tail) =
    (do p <- eval_target_place cx bt;
        write_place cx p (default_value dtv) od) (es with gas_obs := tail)
Proof
  strip_tac >> drule_all immutable_assign_empty_read >> strip_tac >>
  gen_tac >> simp[Once evaluate_def, GSYM bind_assoc] >>
  simp[Once bind_def]
QED
