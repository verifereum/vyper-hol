(* Shared source-side boundary: operator failure precedes every write. *)
Theory augAssignPtrSource
Ancestors
  stmtSimAugAssign gasContext loweringPosts exprBopSimDefs
  vyperInterpreter vyperState vyperMisc stmtSimDefs exprSimDefs

Theorem augassign_pure_prefix_binop_admissible:
  (!gs. eval_target_place cx tgt (es with gas_obs := gs) =
          (INL p,es with gas_obs := gs) /\
        read_place cx p (es with gas_obs := gs) =
          (INL cur,es with gas_obs := gs) /\
        place_type_value cx p (es with gas_obs := gs) =
          (INL ptv,es with gas_obs := gs)) /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx (AugAssign ty tgt bop e)) (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur v ee)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur v ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     ptv bop cur v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur v` >- simp[expr_res_ok_def] >>
  rename1 `_ = INR err` >>
  `eval_stmt cx (AugAssign ty tgt bop e) (es with gas_obs := gs) =
    (INR (Error err),ee)` by
    (rewrite_tac[Once evaluate_def] >>
     simp[GSYM bind_assoc] >>
     first_x_assum (qspec_then `gs` strip_assume_tac) >>
     gvs[bind_def, AllCaseEqs(), lift_sum_def, raise_def]) >>
  drule_all gas_admissible_result >>
  simp[stmt_res_ok_def, expr_res_ok_def]
QED
