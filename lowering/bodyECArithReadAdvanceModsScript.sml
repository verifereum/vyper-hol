Theory bodyECArithReadAdvanceMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  bodyForcedStorageFrameMods exprSimECArith exprSimSource exprSimWordArgs
  exprSimSliceCompose stmtSimForRounds vyperStorageTrace vyperState
  vyperInterpreter exprSimDefs finite_map
Libs
  monadsyntax

(* The empty-tail instance suffices for the source facts at the reached cut. *)
Theorem ec_arith_read_advance_mods:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  expr_body_pre_mods mods ce cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  mid.gas_obs = [] /\
  (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  body_exprs_full_ok_mods mods exps cx rest /\
  expr_sim_inv_mods mods ce cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  value_runtime_typed env (expr_type e) v /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  (?obs. mid.storage_trace = es.storage_trace ++ obs)
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn reset =>
       qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,reset])))) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >> simp[] >>
  conj_tac
  >- (fs[Once body_exprs_full_ok_mods_def] >>
      drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
      qpat_assum `_ ==> body_exprs_full_ok_mods mods exps cx rest` irule >>
      rpt (goal_assum (drule_at Any))) >>
  conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  qpat_assum `bind (eval_expr cx e) _ _ = (INL v,mid)`
    (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
  simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]
QED

Theorem ec_arith_read_admissible_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  gas_admissible (eval_expr cx (Builtin a bt [e1;e2])) expr_vv_res_ok es ==>
  gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es /\
  (!gs v mid. mid.gas_obs = [] /\
    (!tail. bind (eval_expr cx e1) (read_result cx)
       (es with gas_obs := gs ++ tail) = (INL v,mid with gas_obs := tail)) ==>
    gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `bt = ECAdd \/ bt = ECMul` (fn opcode =>
    qpat_x_assum `gas_admissible (eval_expr cx _) _ _`
      (assume_tac o PURE_ONCE_REWRITE_RULE [MATCH_MP ec_eval_bind opcode])) >>
  conj_tac
  >- (drule slice_gas_admissible_expr_head >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  drule_all gas_admissible_bind_tail >> BETA_TAC >>
  qpat_assum `mid with gas_obs := [] = mid` (fn reset => pure_rewrite_tac[reset]) >>
  disch_then (irule o MATCH_MP slice_gas_admissible_expr_head)
QED
