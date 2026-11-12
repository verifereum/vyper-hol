Theory exprSimIfExpWidenedNoCopy
Ancestors
  exprSimIfExpWidenedPosts exprSimIfExpWidenedAdapter
  exprSimLayoutTransport exprSimAggregateChildren exprSimHyps exprSimHypsDefs
  exprSimIfExp exprSimProps exprOperandVar exprLowering context compileEnv
  loweringPosts vyperState vyperAST vyperTypeArgFits vyperTypeSystem exprSimDefs

Theorem nocopy_ifexp_post_annotated:
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  (is_word_type (expr_type e) \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  expr_post ctx func ce cx e es origin sb s0 ee v op q ==>
  expr_post ctx func ce cx (IfExp (expr_type e) c a b) es origin sb s0 ee v op q
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (fs[expr_post_def, expr_type_def] >> metis_tac[]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    (spose_not_then assume_tac >>
     `post_value_type ce e = expr_type e` by
       (irule post_value_type_not_int_call >> metis_tac[]) >> gvs[]) >>
  gvs[expr_type_def] >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv` by
    (rpt strip_tac >> irule expr_sim_inv_memory_size >>
     goal_assum (drule_at Any) >> fs[expr_body_pre_def] >> metis_tac[]) >>
  `arg_type_fits (lowered_value_type ce (Call ann (IntCall fid) args drv)) ann` by
    gvs[type_widens_to_def] >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >>
  gvs[expr_type_def] >>
  `expr_val_rel cx ann v op q` by
    (irule expr_val_rel_layout_transport >> metis_tac[]) >>
  `expr_val_at ce cx ann origin sb ee v op q` by
    (irule expr_val_at_layout_transport >> metis_tac[]) >>
  fs[expr_post_def, expr_type_def] >> metis_tac[]
QED

Theorem nocopy_ifexp_physical_bound:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  (is_word_type (expr_type e) \/
   same_memory_layout ce (lowered_value_type ce e) (expr_type e)) ==>
  !tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (gvs[] >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    (spose_not_then assume_tac >>
     `post_value_type ce e = expr_type e` by
       (irule post_value_type_not_int_call >> metis_tac[]) >> gvs[]) >>
  gvs[expr_type_def] >>
  drule_all ifexp_intcall_copy_source >> strip_tac >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >>
  `!t tv. evaluate_type (get_tenv cx) t = SOME tv ==>
    type_memory_bytes ce t = type_memory_size tv` by
    (rpt strip_tac >> irule expr_sim_inv_memory_size >>
     goal_assum (drule_at Any) >> fs[expr_body_pre_def] >> metis_tac[]) >>
  fs[expr_type_def] >>
  `type_memory_size tvt = type_memory_size tvt'` by
    (irule evaluated_layout_size >>
     qexistsl [`ce`, `ann`, `lowered_value_type ce (Call ann (IntCall fid) args drv)`, `get_tenv cx`] >>
     fs[same_memory_layout_def]) >>
  drule expr_body_pre_copy_ok >>
  disch_then (qspec_then `tvt'` mp_tac) >> simp[expr_type_def]
QED

Theorem compile_nocopy_ifexp_post_frag:
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tvv,ee) /\
  read_result cx tvv ee = (INL v,ee) /\
  (is_word_type (expr_type e) \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
  frag_exec ctx sa sb
    (\s. vv_post ctx func ce cx e es origin sa s0 ee tvv vv s)
    (\q. expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v op q) R
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `unwrap_value ce vv sa = (op,sb)` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[compile_ifexp_arm_def]) >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64` by
    (drule nocopy_ifexp_physical_bound >> simp[] >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  drule_all unwrap_value_materialise_physical_sim >>
  disch_then (qspecl_then [`ctx`, `s0`, `R`] mp_tac) >>
  disch_then (mp_then Any mp_tac fragExecTheory.frag_exec_conseq) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  irule nocopy_ifexp_post_annotated >> metis_tac[]
QED
