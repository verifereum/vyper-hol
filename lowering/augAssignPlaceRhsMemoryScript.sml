(* Typed memory operator readiness at an augmented-place RHS endpoint. *)
Theory augAssignPlaceRhsMemory
Ancestors
  stmtSimAugAssignPlaceMemory bodyBinopFamiliesMemory
  stmtSimAugAssignPlace stmtSimAugAssign exprSimSource exprSimHyps
  exprLowering vyperTypeSystem

Theorem aug_place_rhs_suffix_ready_mem:
  expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type dtv cur /\
  bind (eval_expr cx e) (read_result cx) st = (INL rhs,ee) ==>
  ?tvrhs. evaluate_type (get_tenv cx) (expr_type e) = SOME tvrhs /\
  binop_frag_mem_post (expr_val_rel cx ty) ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty;expr_type e] cur rhs
    (typed_val_to_w256 dtv cur) (typed_val_to_w256 tvrhs rhs) ee
Proof
  strip_tac >>
  `well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL \/ bop = ShR ==> augassign_shift_amount_ok ty e)` by
    metis_tac[aug_place_typing] >>
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_is_word] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >>
  strip_tac >>
  qpat_x_assum `!v. INL rhs = INL v ==> _`
    (qspec_then `rhs` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  rename1 `value_has_type etv rhs` >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> rhs = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==>
      (?i. rhs = IntV i /\ 0 <= i) \/
      (ty = BaseT (BytesT (Fixed 32)) /\
       ?bs. rhs = BytesV bs /\ LENGTH bs = 32))` by
    (strip_tac >> irule augassign_shift_operand >> metis_tac[]) >>
  `(bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n)` by
    (strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  qexists_tac `etv` >> simp[] >>
  irule augassign_binop_frag_typed_mem >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `expr_type e` >> gvs[]
QED
