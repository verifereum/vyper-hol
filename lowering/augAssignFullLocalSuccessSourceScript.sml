(* Actual-RHS source readiness for local AugAssign. *)
Theory augAssignFullLocalSuccessSource
Ancestors
  stmtSimAugAssign augAssignFullSource exprSimSource exprSimHypsDefs
  exprSimProps exprBopSimProps vyperState finite_map list

Theorem augassign_local_success_source_full:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\
  lookup_scopes id es.scopes = SOME entry /\ cur = entry.value /\ ptv = entry.type /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := marks ++ tail) = (INL v,mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  expr_sim_inv cenv cx env mid /\ word_value cur /\
  bop_result cx ty bop [ty;expr_type e] cur v mid = INL w /\ word_value w /\
  value_has_type entry.type w ==>
  evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur v = INL w /\
  (!wr fin. write_place cx (MemoryPlace id []) w (mid with gas_obs := []) = (wr,fin) ==>
    !m. wr <> INR (Error (TypeError m))) /\
  (!current. lookup_scopes id mid.scopes = SOME current ==>
    store_lays_out entry.type current.type w) /\
  (?current. lookup_scopes id mid.scopes = SOME current)
Proof
  strip_tac >>
  `bop <> In /\ bop <> NotIn` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `!bs. cur <> BytesV bs` by metis_tac[word_value_not_bytes] >>
  `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur v = INL w` by
    (`bop_result cx ty bop [ty;expr_type e] cur v mid =
       case evaluate_binop
         (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
         ptv bop cur v of INL w => INL w | INR err => INR (Error err)` by
       (irule bop_result_augassign >> simp[]) >> gvs[AllCaseEqs()]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := marks) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >> disch_then ACCEPT_TAC) >>
  `bop_result cx ty bop [ty;expr_type e] entry.value v
     (mid with gas_obs := []) = INL w` by (simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all augassign_write_admissible >> simp[]) >>
  `FLOOKUP env.var_types id = SOME ty /\ word_value_type ty` by
    (fs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs(),
        vyperTypeSystemTheory.well_typed_target_def,
        vyperTypeEnvTheory.type_place_target_NameTarget] >>
     metis_tac[well_typed_binop_augassign_word]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  conj_tac >- metis_tac[augassign_current_store_layout] >>
  metis_tac[expr_sim_inv_local]
QED
