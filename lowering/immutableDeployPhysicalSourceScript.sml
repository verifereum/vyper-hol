(* Physical source typing for constructor immutable assignment. *)
Theory immutableDeployPhysicalSource
Ancestors
  exprSimHyps exprSimSource exprSimIfExpCompat exprSafeOperand
  assignRelayoutCaller memoryLocalRhsProps valueTypingMemoryProps loweringPosts
  exprSimHypsDefs vyperTypeInvariants exprLowering vyperInterpreter
  valueCopyBytes vyperTypeArgFits
Libs monadsyntax

Theorem immutable_rhs_physical_typed:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) ==>
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  Cases_on `?ann fid args drv. e = Call ann (IntCall fid) args drv`
  >- (qpat_x_assum `?ann fid args drv. _` strip_assume_tac >> gvs[] >>
      drule_all ifexp_intcall_read_physical_typed >> strip_tac >>
      qexists_tac `stv` >> simp[value_has_type_memory_wf] >>
      metis_tac[expr_sim_inv_memory_size]) >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`cx`,`es`,`ee`] >> simp[]) >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  goal_assum (drule_at Any) >> simp[value_has_type_memory_wf]
QED

Theorem immutable_rhs_physical_widens:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty ==>
  type_widens_to (get_tenv cx) (lowered_value_type ce e) dty
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
      well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `env.type_defs = get_tenv cx /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `well_formed_type env.type_defs (expr_type e)` by
    metis_tac[well_typed_expr_type_well_formed] >>
  `type_widens_to env.type_defs (lowered_value_type ce e) (expr_type e)` by
    (drule_all ifexp_lowered_type_classify >> strip_tac
     >- simp[]
     >- simp[vyperTypeSystemTheory.type_widens_to_def] >>
     gvs[] >> drule ifexp_body_pre_intcall_physical >>
     simp[vyperASTTheory.expr_type_def,
          vyperTypeSystemTheory.type_widens_to_def]) >>
  metis_tac[type_widens_to_trans]
QED

Theorem immutable_rhs_post_physical_classify:
  expr_body_pre ce cx env e es ==>
  post_value_type ce e = lowered_value_type ce e \/
  (is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e))
Proof
  strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >> simp[]) >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (qpat_x_assum `?ty fid args drv. _` strip_assume_tac >> gvs[] >>
      simp[post_value_type_def] >>
      Cases_on `is_word_type ty`
      >- metis_tac[compileEnvTheory.type_widens_to_word, vyperASTTheory.expr_type_def] >>
      Cases_on `is_bytestring_type ty` >> simp[] >>
      qpat_x_assum `type_widens_to _ _ _` mp_tac >>
      qmatch_goalsub_abbrev_tac `type_widens_to _ src _` >>
      Cases_on `ty` >> Cases_on `src` >>
      gvs[compileEnvTheory.is_bytestring_type_def,
          vyperASTTheory.expr_type_def,
          vyperTypeSystemTheory.type_widens_to_def,
          vyperTypeSystemTheory.arg_type_fits_def] >>
      Cases_on `b` >> Cases_on `b'` >>
      gvs[compileEnvTheory.is_bytestring_type_def,
          vyperTypeSystemTheory.arg_type_fits_def] >>
      Cases_on `b` >> Cases_on `b''` >>
      gvs[compileEnvTheory.is_bytestring_type_def,
          vyperTypeSystemTheory.arg_type_fits_def]) >>
  `well_typed_expr env e /\
   (!id t. FLOOKUP env.var_types id = SOME t ==>
     well_formed_type env.type_defs t) /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    (conj_tac >- fs[expr_body_pre_def] >> conj_tac
     >- metis_tac[expr_body_pre_var_types_well_formed] >>
     fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def]) >>
  drule_all ifexp_lowered_type_classify >>
  metis_tac[post_value_type_not_int_call]
QED

Theorem immutable_rhs_physical_post_widens:
  expr_body_pre ce cx env e es ==>
  type_widens_to (get_tenv cx) (lowered_value_type ce e) (post_value_type ce e)
Proof
  strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >> simp[]) >>
  Cases_on `e` >> simp[post_value_type_def] >>
  rename1 `Call ty tgt args drv` >> Cases_on `tgt` >>
  simp[post_value_type_def] >>
  gvs[vyperASTTheory.expr_type_def] >> IF_CASES_TAC >> simp[]
QED

Theorem immutable_rhs_physical_memory:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es sa sb s0 ee v op s /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  ~is_word_type (lowered_value_type ce e) ==>
  ?ptv w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
    value_has_type ptv v /\ eval_operand op s = SOME w /\
    val_in_memory stv v (w2n w) s.vs_memory /\
    val_footprint stv v = val_footprint ptv v
Proof
  strip_tac >>
  drule_all immutable_rhs_physical_typed >> strip_tac >> gvs[] >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (post_value_type ce e)` by
    metis_tac[immutable_rhs_physical_post_widens] >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  drule immutable_rhs_post_physical_classify >> strip_tac
  >- (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `~is_word_type (post_value_type ce e)` by metis_tac[is_bytestring_word_type] >>
  `?w. eval_operand op s = SOME w /\ val_in_memory tu v (w2n w) s.vs_memory` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  qexistsl_tac [`tu`,`w`] >> simp[] >> conj_tac
  >- metis_tac[bytestring_val_in_memory_transfer] >>
  metis_tac[bytestring_val_footprint_eq]
QED
