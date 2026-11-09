(* Source-side callbacks for the memory-safe augmented-place suffix. *)
Theory augAssignPlaceSourceMemory
Ancestors
  augAssignPlaceRhsMemory stmtSimAugAssignPlaceStorage
  stmtSimAugAssignPlaceMemory stmtSimAugAssignPlace stmtSimAugAssign
  tupleTargetStoreProps gasContext vyperState bodyMemoryPreds
  exprSimSource exprSimHyps exprSimHypsDefs

Theorem aug_place_memory_suffix_source[local]:
  bop <> In /\ bop <> NotIn /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  gas_admissible
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (MemoryPlace id path)))
    (stmt_res_ok lctx) ee ==>
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    ?ff. write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
      !tail. write_place cx (MemoryPlace id path) v (ee with gas_obs := tail) =
        (INL (),ff with gas_obs := tail))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_admissible suffix _ ee` >>
  Cases_on `suffix ee` >> rename1 `suffix ee = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (irule aug_place_pure_suffix_admissible >>
     gvs[Abbr `suffix`] >> metis_tac[]) >>
  `case bop_result cx ty bop [ty;expr_type e] cur rhs ee of
     INR ex => res = INR ex /\ ff = ee
   | INL v => write_place cx (MemoryPlace id path) v ee = (res,ff)` by
    (`bop_result cx ty bop [ty;expr_type e] cur rhs ee =
      case evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
       (irule bop_result_augassign >> simp[]) >>
     pop_assum SUBST1_TAC >>
     qpat_x_assum `suffix ee = _` mp_tac >>
     simp[Abbr `suffix`, bind_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       ptv bop cur rhs` >> simp[return_def, raise_def] >> metis_tac[]) >>
  conj_tac
  >- (irule aug_place_bop_write_result_ok >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  `res = INL ()` by (irule aug_place_memory_write_success >> metis_tac[]) >>
  gvs[] >> drule aug_place_memory_write_gas_obs >> simp[]
QED

Theorem aug_place_rhs_typed_memory_source[local]:
  expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type dtv cur /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := gs) = (INL rhs,ee) ==>
  word_value rhs /\ expr_sim_inv cenv cx env ee /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty;expr_type e] cur rhs ee /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    value_has_type dtv v)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (st with gas_obs := gs)` by simp[] >>
  drule_all aug_place_rhs_suffix_ready >> strip_tac >>
  drule_all aug_place_rhs_suffix_ready_mem >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  drule_all (REWRITE_RULE [ETA_AX] exprSimSourceTheory.expr_body_pre_word_result) >>
  strip_tac >> simp[] >> metis_tac[exprSimSourceTheory.word_value_type_word]
QED

Theorem aug_place_storage_suffix_source[local]:
  ~cx.txn.is_static /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    value_has_type tv v) ==>
  !v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    ?ff. write_place cx (StoragePlace tr slot tv) v ee = (INL (),ff) /\
      !tail. write_place cx (StoragePlace tr slot tv) v (ee with gas_obs := tail) =
        (INL (),ff with gas_obs := tail)
Proof
  rpt strip_tac >>
  `value_has_type tv v` by metis_tac[] >>
  drule_all tuple_target_storage_write_safe >>
  disch_then (qspecl_then [`tr`, `slot`, `ee`] strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  drule aug_place_storage_write_gas_obs >> simp[]
QED

Theorem aug_place_rhs_reached_mem:
  (!s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx bt s = (INL p,s1) /\
    read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  eval_target_place cx bt (es with gas_obs := gs) = (INL p,st) /\
  read_place cx p st = (INL cur,stc) /\
  place_type_value cx p stc = (INL ptv,stt) ==>
  expr_body_pre cenv cx env e stt /\
  expr_sim_mem ctx func cenv cx ty e stt /\
  expr_vv_sim_mem ctx func cenv cx ty e stt
Proof
  strip_tac >>
  `stc = st /\ stt = stc` by
    metis_tac[read_place_state, place_type_value_state] >> gvs[] >>
  `expr_body_pre cenv cx env e st` by
    (irule aug_place_rhs_pre_target_gas_obs >> goal_assum (drule_at Any) >> simp[]) >>
  `body_expr_mem_ok cx e` by metis_tac[] >>
  gvs[body_expr_mem_ok_def] >> metis_tac[]
QED

Theorem aug_place_memory_rhs_callback:
  expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type dtv cur /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := gs) = (INL rhs,ee) /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  gas_admissible
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (MemoryPlace id path)))
    (stmt_res_ok lctx) ee ==>
  word_value rhs /\ expr_sim_inv cenv cx env ee /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty;expr_type e] cur rhs ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    value_has_type dtv v /\
    ?ff. write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
      !tail. write_place cx (MemoryPlace id path) v (ee with gas_obs := tail) =
        (INL (),ff with gas_obs := tail))
Proof
  strip_tac >> drule_all aug_place_rhs_typed_memory_source >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  drule_all aug_place_memory_suffix_source >> strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem aug_place_storage_rhs_callback:
  expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv cur /\ ~cx.txn.is_static /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := gs) = (INL rhs,ee) /\
  gas_admissible
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (stmt_res_ok lctx) st ==>
  word_value rhs /\ expr_sim_inv cenv cx env ee /\
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty;expr_type e] cur rhs ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    value_has_type tv v /\
    ?ff. write_place cx (StoragePlace tr slot tv) v ee = (INL (),ff) /\
      !tail. write_place cx (StoragePlace tr slot tv) v (ee with gas_obs := tail) =
        (INL (),ff with gas_obs := tail))
Proof
  strip_tac >> drule_all aug_place_rhs_typed_memory_source >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  drule_all aug_place_storage_binop_admissible >> strip_tac >>
  metis_tac[aug_place_storage_suffix_source]
QED
