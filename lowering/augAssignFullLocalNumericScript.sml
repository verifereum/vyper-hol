(* Actual local AugAssign source evaluation supplies the numeric witness. *)
Theory augAssignFullLocalNumeric
Ancestors
  stmtSimAugAssign augAssignPtrTypedNumeric exprSimSource exprSimProps
  exprSimHypsDefs exprSimHyps exprLoweringProps vyperTypeEnv vyperTypeSystem
  vyperTypeStatePreservation
  finite_map list

Theorem augassign_local_numeric_ready_full:
  type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\
  lookup_scopes id es.scopes = SOME entry /\
  gas_admissible (eval_stmt cx (AugAssign ty (NameTarget id) bop e))
    (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  expr_sim_inv cenv cx env ee /\ FLOOKUP env.var_types id = SOME ty /\
  word_value_type ty /\ bop <> In /\ bop <> NotIn /\
  (!w. bop_result cx ty bop [ty;expr_type e] entry.value v ee = INL w ==>
    value_has_type entry.type w) /\
  ((?w. bop_result cx ty bop [ty;expr_type e] entry.value v ee = INL w /\
    word_value w /\
    !x y sa sb op ss.
      compile_binop bop x y ty NONE (if bop = Exp then expr_int_literal e else NONE) sa = (op,sb) /\
      fresh_vars_wrt sa ss /\
      eval_operand x ss = SOME (val_to_w256 entry.value) /\
      eval_operand y ss = SOME (val_to_w256 v) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
        eval_operand op ss' = SOME (val_to_w256 w)) \/
   (?msg. bop_result cx ty bop [ty;expr_type e] entry.value v ee = INR (Error (RuntimeError msg)) /\
    !x y sa sb op ss.
      compile_binop bop x y ty NONE (if bop = Exp then expr_int_literal e else NONE) sa = (op,sb) /\
      fresh_vars_wrt sa ss /\
      eval_operand x ss = SOME (val_to_w256 entry.value) /\
      eval_operand y ss = SOME (val_to_w256 v) ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss'))
Proof
  strip_tac >>
  `FLOOKUP env.var_types id = SOME ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   augassign_operand_ok ty bop e` by
    gvs[type_stmt_def, well_typed_target_def, type_place_target_NameTarget, AllCaseEqs()] >>
  drule augassign_operand_ok_operands >> strip_tac >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  drule_all augassign_binop_ready >>
  disch_then (qspecl_then [`func`, `ee`, `ctx`] strip_assume_tac) >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  simp[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by
    metis_tac[expr_sim_inv_local] >>
  `value_has_type entry.type entry.value` by
    metis_tac[expr_sim_inv_def, lookup_scopes_state_well_typed_value_has_type] >>
  `well_formed_type env.type_defs ty` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >> strip_tac >> gvs[] >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount] >>
  drule_all augassign_binop_admissible >> disch_tac >>
  irule binop_typed_numeric_witness >> simp[] >>
  conj_tac
  >- (strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
      Cases_on `expr_int_literal e` >> gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`expr_type e`, `get_tenv cx`, `entry.type`, `tyv`] >> simp[]
QED
