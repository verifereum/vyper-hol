(* Storage-place source boundary, independent of the target spelling. *)
Theory augAssignPtrStoragePlaceSource
Ancestors
  augAssignPtrStorageCommon augAssignPtrSource stmtSimAugAssignStorage
  gasContext loweringPosts vyperInterpreter vyperState vyperExprNoControl
  stmtSimDefs exprSimDefs
Libs monadsyntax

Theorem eval_augassign_storage_place_ptr:
  eval_target_place cx tgt es = (INL (StoragePlace tr slot tv),es) /\
  read_storage_slot cx tr slot tv es = (INL cur,es) ==>
  eval_stmt cx (AugAssign ty tgt bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v);
      write_storage_slot cx tr slot tv r od) es
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, read_place_def,
       place_type_value_def, return_def, write_place_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem augassign_storage_place_exception_ptr:
  eval_target_place cx tgt es = (INL (StoragePlace tr slot tv),es) /\
  read_storage_slot cx tr slot tv es = (INL cur,es) /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex,ee) ==>
  eval_stmt cx (AugAssign ty tgt bop e) es = (INR ex,ee)
Proof
  strip_tac >> drule_all eval_augassign_storage_place_ptr >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, Once bind_def]
QED

Theorem augassign_storage_place_normal_ptr:
  eval_target_place cx tgt es = (INL (StoragePlace tr slot tv),es) /\
  read_storage_slot cx tr slot tv es = (INL cur,es) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  eval_stmt cx (AugAssign ty tgt bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop cur v)) (write_storage_slot cx tr slot tv) ee
Proof
  strip_tac >> drule_all eval_augassign_storage_place_ptr >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  simp[GSYM bind_assoc, Once bind_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem augassign_storage_place_admissible_ptr:
  (!gs. eval_target_place cx tgt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tv),es with gas_obs := gs)) /\
  read_storage_slot cx tr slot tv es = (INL cur,es) /\
  gas_admissible (eval_stmt cx (AugAssign ty tgt bop e)) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  `read_storage_slot cx tr slot tv (es with gas_obs := gs) =
     (INL cur,es with gas_obs := gs)` by
    metis_tac[read_storage_slot_gas_obs_ptr] >>
  `eval_target_place cx tgt (es with gas_obs := gs) =
     (INL (StoragePlace tr slot tv),es with gas_obs := gs)` by simp[] >>
  drule_all augassign_storage_place_exception_ptr >>
  disch_then (qspecl_then [`ty`, `bop`] assume_tac) >>
  `no_control_exc y` by
    (qpat_x_assum `bind _ _ _ = (INR y,_)` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control, read_result_no_control]) >>
  drule_all gas_admissible_result >>
  Cases_on `y` >> gvs[no_control_exc_def, stmt_res_ok_def, expr_res_ok_def]
QED
