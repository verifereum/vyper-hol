(* Empty-path immutable augmented-assignment entry interfaces. *)
Theory immutableAugAssignRootEntry
Ancestors
  bodyAugAssignOther bodyAugPlaceTarget bodyImmutableAugAssignFacts
  immutableAugAssignRootPrefix
  augAssignPlaceCompileMemory bodyStorageMetadata vyperTypeEnv
  supportedStmts supportedExprForms supportedTypes vyperTypeSystem vyperTypeInvariants

Theorem immutable_augassign_root_metadata:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  immutable_root cx (TopLevelNameTarget (src,id)) ==>
  ?ts off tv iv.
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE /\
    src = cenv.ce_module /\ cx.in_deploy /\ cenv.ce_is_ctor /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    FLOOKUP env.bare_global_assignable (src,id) = SOME ty /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    off + type_memory_size tv < dimword (:256) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
               NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
      SOME (tv,iv) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e)
Proof
  strip_tac >>
  drule stmtSimAugAssignPlaceTheory.aug_place_typing >> strip_tac >>
  `get_module_code cx NONE = SOME tops` by fs[bodySimTheory.body_inv_def] >>
  `?ts. get_module_code cx src = SOME ts /\
        find_var_decl_by_name id ts = NONE` by
    gvs[targetPlaceSimTheory.immutable_root_def,
        targetPlaceSimTheory.target_root_def] >>
  `~supported_aug_target tops bindings (TopLevelNameTarget (src,id))` by
    (spose_not_then assume_tac >>
     drule supported_aug_toplevel_decl >> strip_tac >> gvs[] >>
     metis_tac[aug_storage_decl_some]) >>
  `~supported_scalar_target tops (src,id)` by
    (spose_not_then assume_tac >>
     qpat_x_assum `supported_scalar_target _ _` mp_tac >>
     simp[supported_scalar_target_def] >>
     Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
     rename1 `_ = SOME decl` >> PairCases_on `decl` >>
     Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
     simp[] >> strip_tac >>
     drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
     metis_tac[aug_storage_decl_some]) >>
  `?ity. supported_immutable_type tops (src,id) = SOME ity` by
    fs[supported_stmt_def, supported_target_def, optionTheory.IS_SOME_EXISTS] >>
  `cx.in_deploy` by
    (spose_not_then assume_tac >>
     `env_context_consistent env cx` by
       fs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def] >>
     drule_all augassign_immutable_runtime_untyped >> gvs[]) >>
  drule_all immutable_augassign_metadata >> strip_tac >> gvs[] >>
  drule_all immutable_augassign_entry >> strip_tac >>
  `FLOOKUP env.bare_global_assignable (cenv.ce_module,id) = SOME ity` by
    (Cases_on `FLOOKUP env.bare_global_assignable (cenv.ce_module,id)` >>
     gvs[type_place_target_TopLevelNameTarget]) >>
  simp[] >> metis_tac[]
QED

Theorem immutable_augassign_root_entry:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  immutable_root cx (TopLevelNameTarget (src,id)) /\
  stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e)
    sa = (c,sf) /\ fn_has_code sa sf func /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  c = cenv /\ ?off tv iv cur rhs result s1 s2 s3 u.
    cenv.ce_is_ctor /\ src = cenv.ce_module /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv iv /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (src,id) = SOME ty /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (ImmutablePlace src id []),es) /\
    read_place cx (ImmutablePlace src id []) es = (INL iv,es) /\
    place_type_value cx (ImmutablePlace src id []) es = (INL tv,es) /\
    emit_op MLOAD [Lit (n2w off)] sa = (cur,s1) /\
    lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
    compile_binop bop cur rhs ty NONE
      (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
    emit_void MSTORE [Lit (n2w off);result] s3 = ((),sf) /\
    fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
    local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
    local_ptrs_reserved cenv s3 /\
    (!z. not_fresh_at s1 z ==> not_fresh_at s2 z) /\
    (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
    gas_marked_path T ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ alloca_history func u /\
    eval_operand cur u = SOME (typed_val_to_w256 tv iv) /\
    w2n (n2w off : bytes32) + 32 <= u.vs_alloca_next /\
    (!z. cur = Var z ==> not_fresh_at s1 z) /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = s1.cs_current_bb /\
    u.vs_inst_idx = LENGTH s1.cs_current_insts /\ (!l. cur <> Label l)
Proof
  strip_tac >> drule_all immutable_augassign_root_metadata >> strip_tac >>
  drule stmtSimAugAssignPlaceTheory.aug_place_typing >> strip_tac >>
  `is_word_type ty` by metis_tac[exprSimSourceTheory.word_value_type_word] >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >> metis_tac[]) >>
  drule_all immutable_augassign_entry >> strip_tac >> gvs[] >>
  drule_all immutable_augassign_source_prefix >> strip_tac >>
  drule_all immutable_augassign_load >> strip_tac >>
  `type_memory_size tv = 32` by metis_tac[exprSimPropsTheory.word_tv_memory_size] >>
  `off + type_memory_size tv <= s.vs_alloca_next` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
        exprLoweringPropsTheory.immutable_alloca_sep_def] >>
     first_x_assum drule_all >> simp[]) >>
  drule_all immutable_augassign_root_compilation >> strip_tac >> gvs[] >>
  drule immutable_augassign_root_prefix_mem >>
  simp[] >> disch_then drule_all >> strip_tac >>
  simp[] >> metis_tac[]
QED
