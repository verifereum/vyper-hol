(* The first two modular operands survive the later operand evaluations. *)
Theory bodyWordModThirdEntryMods
Ancestors
  bodyFullPostsMods bodyPtrDefs exprBopSimProps loweringPosts
  loweringShapeDefs compileEnv valueEncoding vyperValue ptrDiscipline

Theorem uint256_post_operand[local]:
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_type e = BaseT (UintT 256) ==>
  eval_operand op t = SOME (val_to_w256 v)
Proof
  simp[expr_post_mods_def, expr_post_def] >> strip_tac >>
  `post_value_type cenv e = BaseT (UintT 256)` by
    (qpat_assum `expr_type e = _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     irule post_value_type_word >> simp[is_word_type_def]) >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def, is_word_type_def, evaluate_type_def] >>
  Cases_on `v` >> simp[typed_val_to_w256_def]
QED

Theorem modular_operand_kept[local]:
  expr_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sb t ee v out u /\
  ghost_kept_at lo cenv es sa G tn t G' tn' /\
  (!q. op = Var q ==> not_fresh_at sa q) /\ (!l. op <> Label l) /\
  eval_operand op t = SOME w /\ op_taint tn op = {} ==>
  eval_operand op u = SOME w /\ op_taint tn' op = {}
Proof
  strip_tac >> conj_tac
  >- (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`,`t`] >>
      fs[expr_post_mods_def, expr_post_def]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  Cases_on `op` >> fs[op_taint_def] >>
  first_x_assum (drule_then strip_assume_tac) >> fs[op_taint_def]
QED

Theorem modular_operands_at_third_cut_mods:
  expr_type e1 = BaseT (UintT 256) /\
  expr_type e2 = BaseT (UintT 256) /\
  expr_type e3 = BaseT (UintT 256) /\
  expr_post_mods (H1 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e1 es sa s1 s0 mid1 v1 x t1 /\
  expr_post_mods (H2 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e2 mid1 s1 s2 t1 mid2 v2 y t2 /\
  expr_post_mods (H3 : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e3 mid2 s2 s3 t2 fin v3 z t3 /\
  ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t1 /\
  ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 t2 /\
  ptr_val_ok cx (post_value_type cenv e3) v3 z G3 tn3 t3 /\
  ghost_kept_at lo cenv mid1 s1 G1 tn1 t1 G2 tn2 /\
  ghost_kept_at lo cenv mid2 s2 G2 tn2 t2 G3 tn3 /\
  s1.cs_next_var <= s2.cs_next_var /\
  (!q. x = Var q ==> not_fresh_at s1 q) /\
  (!q. y = Var q ==> not_fresh_at s2 q) /\
  (!l. x <> Label l) /\ (!l. y <> Label l) ==>
  eval_operand x t3 = SOME (val_to_w256 v1) /\
  eval_operand y t3 = SOME (val_to_w256 v2) /\
  eval_operand z t3 = SOME (val_to_w256 v3) /\
  op_taint tn3 x = {} /\ op_taint tn3 y = {} /\ op_taint tn3 z = {}
Proof
  strip_tac >> fs[ptr_val_ok_def] >>
  `eval_operand x t1 = SOME (val_to_w256 v1)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac uint256_post_operand) >> simp[]) >>
  `eval_operand y t2 = SOME (val_to_w256 v2)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac uint256_post_operand) >> simp[]) >>
  `eval_operand z t3 = SOME (val_to_w256 v3)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ e3 _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac uint256_post_operand) >> simp[]) >>
  `!q. x = Var q ==> not_fresh_at s2 q` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `s1` >> simp[]) >>
  `eval_operand x t2 = SOME (val_to_w256 v1) /\ op_taint tn2 x = {}` by
    (qpat_assum `ghost_kept_at _ _ _ s1 _ _ _ _ _`
       (mp_then Any irule modular_operand_kept) >> simp[] >>
     qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _` (irule_at Any)) >>
  `eval_operand x t3 = SOME (val_to_w256 v1) /\ op_taint tn3 x = {}` by
    (qpat_assum `ghost_kept_at _ _ _ s2 _ _ _ _ _`
       (mp_then Any irule modular_operand_kept) >> simp[] >>
     qpat_assum `expr_post_mods _ _ _ _ _ e3 _ _ _ _ _ _ _ _` (irule_at Any)) >>
  `eval_operand y t3 = SOME (val_to_w256 v2) /\ op_taint tn3 y = {}` by
    (qpat_assum `ghost_kept_at _ _ _ s2 _ _ _ _ _`
       (mp_then Any irule modular_operand_kept) >> simp[] >>
     qpat_assum `expr_post_mods _ _ _ _ _ e3 _ _ _ _ _ _ _ _` (irule_at Any)) >>
  simp[]
QED
