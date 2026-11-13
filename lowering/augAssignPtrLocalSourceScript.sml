(* Counted source-action boundaries absent from this tree's older S1 copy. *)
Theory augAssignPtrLocalSource
Ancestors
  stmtSimAugAssign bodyPtrDefs gasContext gasSummaryComposePtr
  exprSimDefs stmtSimDefs
  vyperInterpreter vyperLookup vyperExprNoControl vyperState
Libs
  monadsyntax

Theorem eval_augassign_local_forced_ptr:
  lookup_scopes id es.scopes = SOME entry ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
        entry.type bop entry.value v);
      write_place cx (MemoryPlace id []) r od) es
Proof
  strip_tac >>
  drule_then (qspec_then `cx` strip_assume_tac) eval_target_place_local >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem augassign_rhs_admissible_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `eval_stmt cx (AugAssign ty (NameTarget id) bop e)
     (es with gas_obs := gs) = (INR ex, ee)` by
    (`lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
     drule eval_augassign_local_forced_ptr >>
     disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
     simp[bind_def]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

Theorem augassign_rhs_exception_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex, ee) ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (INR ex, ee)
Proof
  strip_tac >> drule eval_augassign_local_forced_ptr >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[bind_def]
QED

Theorem augassign_rhs_normal_ptr:
  lookup_scopes id es.scopes = SOME entry /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
    entry.type bop entry.value v))
    (write_place cx (MemoryPlace id [])) ee
Proof
  strip_tac >> drule eval_augassign_local_forced_ptr >>
  disch_then (qspecl_then [`ty`, `e`, `cx`, `bop`] mp_tac) >>
  simp[Once bind_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem augassign_write_admissible_ptr:
  lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) /\
  bop_result cx ty bop [ty; expr_type e] entry.value v ee = INL w /\
  write_place cx (MemoryPlace id []) w ee = (res, fin) ==>
  !m. res <> INR (Error (TypeError m))
Proof
  strip_tac >>
  `?actual. evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     entry.type bop entry.value v = INL actual` by
    metis_tac[bop_result_augassign_success] >>
  Cases_on `write_place cx (MemoryPlace id []) actual ee` >>
  rename1 `_ = (actual_res, actual_fin)` >>
  `eval_stmt cx (AugAssign ty (NameTarget id) bop e)
     (es with gas_obs := gs) = (actual_res, actual_fin)` by
    (`lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
     drule_all augassign_rhs_normal_ptr >>
     disch_then (qspecl_then [`ty`, `bop`] mp_tac) >>
     simp[lift_sum_def, bind_def, return_def]) >>
  `stmt_res_ok lctx actual_res` by metis_tac[gas_admissible_result] >>
  `res = actual_res` by
    (qspecl_then [`[]`, `cx`, `id`, `w`, `ee`, `actual`]
       mp_tac write_place_short_memory_result >> simp[]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED
