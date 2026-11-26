(* Save the start operand across the reached Slice length evaluation. *)
Theory bodySliceSavedWordsMods
Ancestors
  bodyFullPostsMods bodyPtrDefs exprBopSimProps loweringPosts loweringShapeDefs
  compileEnv valueEncoding vyperValue ptrDiscipline exprBodyPreProps
  exprWordOperand exprSimSource vyperTypeEvalCaseProofs vyperTypeInvariants vyperTypeSystem

Theorem slice_word_shape[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  lower_value compile_expr cenv ty e sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!q. op = Var q ==> not_fresh_at sb q) /\ (!l. op <> Label l)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all lower_value_word_shape >> simp[]
QED

Theorem slice_word_post[local]:
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_type e = BaseT (UintT 256) /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t ==>
  eval_operand op t = SOME (val_to_w256 v) /\
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `post_value_type cenv e = BaseT (UintT 256)` by
    (qpat_assum `expr_type e = _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     irule post_value_type_word >> simp[is_word_type_def]) >>
  fs[ptr_val_ok_def, is_word_type_def] >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_mods_def, expr_post_def] >> strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def, is_word_type_def, evaluate_type_def] >>
  Cases_on `v` >> simp[typed_val_to_w256_def]
QED

Theorem slice_word_kept[local]:
  expr_post_mods H ctx func cenv cx e es sa sb t ee v out u /\
  ghost_kept_at lo cenv es sa G tn t G' tn' /\
  (!q. op = Var q ==> not_fresh_at sa q) /\ (!l. op <> Label l) /\
  eval_operand op t = SOME w /\ op_prov G op = NONE /\ op_taint tn op = {} ==>
  eval_operand op u = SOME w /\ op_prov G' op = NONE /\ op_taint tn' op = {}
Proof
  strip_tac >> conj_tac
  >- (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`,`t`] >>
      fs[expr_post_mods_def, expr_post_def]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  Cases_on `op` >> fs[op_prov_def, op_taint_def] >>
  first_x_assum (drule_then strip_assume_tac) >> fs[op_taint_def]
QED

Theorem slice_saved_words_mods:
  expr_body_pre_mods mods cenv cx env1 start es /\
  expr_body_pre_mods mods cenv cx env2 len mid /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  lower_value compile_expr cenv ty1 start sa = (x,s1) /\
  lower_value compile_expr cenv ty2 len s1 = (y,s2) /\
  expr_post_mods H1 ctx func cenv cx start es sa s1 s0 mid v1 x t1 /\
  expr_post_mods H2 ctx func cenv cx len mid s1 s2 t1 ee v2 y t2 /\
  ptr_val_ok cx (post_value_type cenv start) v1 x G1 tn1 t1 /\
  ptr_val_ok cx (post_value_type cenv len) v2 y G2 tn2 t2 /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t1 G2 tn2 ==>
  eval_operand x t2 = SOME (val_to_w256 v1) /\
  eval_operand y t2 = SOME (val_to_w256 v2) /\
  op_prov G2 x = NONE /\ op_prov G2 y = NONE /\
  op_taint tn2 x = {} /\ op_taint tn2 y = {} /\
  (!q. x = Var q ==> not_fresh_at s2 q) /\
  (!q. y = Var q ==> not_fresh_at s2 q) /\
  (!l. x <> Label l) /\ (!l. y <> Label l)
Proof
  strip_tac >>
  qpat_assum `lower_value _ _ _ start _ = _`
    (mp_then Any (drule_all_then strip_assume_tac) slice_word_shape) >>
  qpat_assum `lower_value _ _ _ len _ = _`
    (mp_then Any (drule_all_then strip_assume_tac) slice_word_shape) >>
  qpat_assum `expr_post_mods _ _ _ _ _ start _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) slice_word_post) >>
  qpat_assum `expr_post_mods _ _ _ _ _ len _ _ _ _ _ _ _ _`
    (mp_then Any (drule_all_then strip_assume_tac) slice_word_post) >>
  `eval_operand x t2 = SOME (val_to_w256 v1) /\
   op_prov G2 x = NONE /\ op_taint tn2 x = {}` by
    (qpat_assum `expr_post_mods _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any (drule_all_then ACCEPT_TAC) slice_word_kept)) >>
  simp[] >> rpt strip_tac >>
  irule not_fresh_at_mono >> qexists_tac `s1` >> simp[]
QED
