(* Typed memory operator readiness at an augmented-place RHS endpoint. *)
Theory augAssignPlaceRhsMemory
Ancestors
  stmtSimAugAssignPlaceMemory bodyBinopFamiliesMemory
  stmtSimAugAssignPlace exprSimSource exprSimHyps exprLowering vyperTypeSystem

Theorem aug_place_rhs_suffix_ready_mem:
  expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type dtv cur /\
  bind (eval_expr cx e) (read_result cx) st = (INL rhs,ee) ==>
  binop_frag_val_mem ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty;expr_type e] cur rhs ee
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  rename1 `value_has_type etv rhs` >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> rhs = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i)` by
    (disch_tac >>
     `shift_amount_ok e` by metis_tac[] >>
     drule_all eval_expr_shift_amount >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ty`, `Name ty id`, `e`,
    `cur`, `rhs`, `ee`, `dtv`, `etv`] mp_tac binop_frag_typed_mem >>
  simp[vyperASTTheory.expr_type_def, expr_int_literal_def] >>
  disch_then irule >>
  strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
  Cases_on `expr_int_literal e` >> gvs[]
QED
