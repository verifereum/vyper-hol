(* Source replay and operand preparation at the reached AugAssign RHS cut. *)
Theory bodyAugRhsOperatorReadyMods
Ancestors
  augAssignFullOperandReady augAssignFullOperatorSource augAssignFullSourceReplay
  bodySimStmtFacts bodyWriteSubscriptSourceMods bodyFullPostsMods exprBodyPreProps
  exprWordOperand exprBopSimProps exprSimSource stmtSimAugAssignPlace stmtSimAugAssign
  freshWrites vyperTypeEvalCaseProofs vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem loweringPosts bodyPtrDefs
Libs
  monadsyntax

Theorem augassign_rhs_value_type_mods[local]:
  expr_body_pre_mods mods cenv cx env e st /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := reads) = (INL rhs,ee) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv rhs
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (st with gas_obs := reads)` by simp[] >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  simp[value_runtime_typed_def]
QED

Theorem augassign_rhs_word_shape_mods[local]:
  expr_body_pre_mods mods cenv cx env e st /\ is_word_type (expr_type e) /\
  lower_value compile_expr cenv ty e sa = (rhsop,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!x. rhsop = Var x ==> not_fresh_at sb x) /\ (!l. rhsop <> Label l)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  drule_all lower_value_word_shape >> simp[]
QED

Theorem augassign_rhs_operator_ready_mods:
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre_mods mods cenv cx env e st /\
  (!gs. eval_target_place cx bt (entry with gas_obs := preT ++ gs) =
        (INL p,st with gas_obs := gs)) /\
  read_place cx p st = (INL cur,st) /\
  place_type_value cx p st = (INL ptv,st) /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
  (!gs. bind (eval_expr cx e) (read_result cx) (st with gas_obs := preE ++ gs) =
        (INL rhs,ee with gas_obs := gs)) /\
  ee.gas_obs = [] /\
  lower_value compile_expr cenv ty e sa = (rhsop,sb) /\
  expr_post_mods H ctx func cenv cx e st sa sb s0 ee rhs rhsop s /\
  ptr_val_ok cx (post_value_type cenv e) rhs rhsop G tn s /\
  (!x. old = Var x ==> not_fresh_at sa x) /\ (!l. old <> Label l) ==>
  ?tvR. evaluate_type (get_tenv cx) (expr_type e) = SOME tvR /\
    value_has_type tvR rhs /\ eval_operand rhsop s = SOME (typed_val_to_w256 tvR rhs) /\
    op_prov G rhsop = NONE /\ op_taint tn rhsop = {} /\
    (!x. old = Var x ==> not_fresh_at sb x) /\
    (!x. rhsop = Var x ==> not_fresh_at sb x) /\
    (!l. old <> Label l /\ rhsop <> Label l) /\
    sa.cs_next_var <= sb.cs_next_var /\ type_bits ty MOD 8 = 0 /\ is_word_type ty /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
    (bop = Exp ==>
      (?n. (if bop = Exp then expr_int_literal e else NONE) = SOME n /\ 0 <= n) /\
      (!n. (if bop = Exp then expr_int_literal e else NONE) = SOME n ==> rhs = IntV n)) /\
    (bop = ShL \/ bop = ShR ==>
      (?i. rhs = IntV i /\ 0 <= i) \/
      (ty = BaseT (BytesT (Fixed 32)) /\ ?bs. rhs = BytesV bs /\ LENGTH bs = 32)) /\
    (!gs. eval_stmt cx (AugAssign ty bt bop e)
            (entry with gas_obs := (preT ++ preE) ++ gs) =
          bind (lift_sum (evaluate_binop
            (case type_to_int_bound ty of SOME n => n | NONE => Unsigned 0)
            ptv bop cur rhs)) (write_place cx p) (ee with gas_obs := gs)) /\
    (case evaluate_binop
       (case type_to_int_bound ty of SOME n => n | NONE => Unsigned 0) ptv bop cur rhs of
       INL v => bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v /\
                value_has_type ptv v
     | INR err => ?msg. err = RuntimeError msg /\
                 bop_result cx ty bop [ty;expr_type e] cur rhs ee =
                 INR (Error (RuntimeError msg)))
Proof
  strip_tac >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (st with gas_obs := preE) = (INL rhs,ee)` by
    (pop_assum (fn upd => first_assum
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL, upd])))) >>
  drule_all_then strip_assume_tac augassign_rhs_value_type_mods >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] augassign_joint_operand_ready) >>
  drule_all_then strip_assume_tac well_typed_binop_augassign_is_word >>
  drule_all_then strip_assume_tac augassign_rhs_word_shape_mods >>
  `!x. old = Var x ==> not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
  `type_bits ty MOD 8 = 0` by
    (drule aug_place_typing >> strip_tac >>
     qpat_assum `assignable_type _ ty`
       (ACCEPT_TAC o MATCH_MP well_formed_type_bits o MATCH_MP assignable_type_well_formed)) >>
  `expr_val_rel cx (expr_type e) rhs rhsop s /\
   op_prov G rhsop = NONE /\ op_taint tn rhsop = {}` by
     fs[expr_post_mods_def, expr_post_def, ptr_val_ok_def] >>
  drule_all_then assume_tac expr_val_rel_typed >>
  qexists_tac `tv` >> asm_rewrite_tac [] >> simp[] >>
  conj_tac >- (irule augassign_source_prefix_replay >>
               rpt (first_assum (irule_at Any)) >> asm_rewrite_tac []) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME n => n | NONE => Unsigned 0) ptv bop cur rhs` >>
  simp[Once sumTheory.sum_case_def]
  >- (conj_tac
      >- (drule_all augassign_operator_source_representation >> simp[])
      >> drule_all augassign_operator_source_value_type >> simp[]) >>
  drule_all augassign_operator_source_runtime_error >> simp[]
QED
