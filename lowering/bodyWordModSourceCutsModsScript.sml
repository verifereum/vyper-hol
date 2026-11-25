(* Source cuts for AddMod and MulMod: the next IH requires a forced success. *)
Theory bodyWordModSourceCutsMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  exprBodyPreProps exprSimWordBuiltins exprSimWordArgs exprSimSource
  exprSimHypsDefs exprSimAbiDecodeEntryTyping supportedExprTraverse
  supportedProgram allocLimits constSubstCorrect
  vyperTypeBuiltins vyperTypeSystem vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeCallGraph vyperContext vyperInterpreter vyperState vyperAST vyperValue
  valueEncoding list

Theorem modular_child_pre[local]:
  (bt = AddMod \/ bt = MulMod) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann bt args) es /\
  MEM e args /\ expr_sim_inv_mods mods cenv cx env mid ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `bt = AddMod \/ bt = MulMod` strip_assume_tac >> gvs[] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
  rw[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
     supported_exprs_exists_every, EXISTS_MEM] >>
  gvs[expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem,
            int_calls_exprs_every_mem]
QED

Theorem modular_source_shape_mods:
  (bt = AddMod \/ bt = MulMod) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann bt args) es ==>
  ?e1 e2 e3. args = [e1;e2;e3] /\ ann = BaseT (UintT 256) /\
    EVERY (\e. expr_type e = BaseT (UintT 256)) args /\
    expr_sim_inv_mods mods cenv cx env es /\
    (!e mid. MEM e args /\ expr_sim_inv_mods mods cenv cx env mid ==>
      expr_body_pre_mods mods cenv cx env e mid)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >> strip_tac >>
  `ann = BaseT (UintT 256) /\
   MAP expr_type args = [BaseT (UintT 256);BaseT (UintT 256);BaseT (UintT 256)]` by
    (qpat_x_assum `bt = AddMod \/ bt = MulMod` strip_assume_tac >> gvs[]
     >- (drule (SIMP_RULE (srw_ss()) [] (Q.SPECL [`ann`,`AddMod`] word_builtin_modular_types)) >> simp[]) >>
     drule (SIMP_RULE (srw_ss()) [] (Q.SPECL [`ann`,`MulMod`] word_builtin_modular_types)) >> simp[])
  >>
  qpat_x_assum `MAP expr_type args = _` mp_tac >>
  simp[MAP_EQ_CONS, MAP_EQ_NIL] >> strip_tac >> gvs[] >>
  drule_at (Pat `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _`) modular_child_pre >>
  simp[] >> metis_tac[]
QED

Theorem modular_forced_action:
  (bt = AddMod \/ bt = MulMod) ==>
  bind (eval_expr cx (Builtin ann bt [e1;e2;e3])) (read_result cx) =
  bind (bind (eval_expr cx e1) (read_result cx)) (\v1.
    bind (bind (eval_expr cx e2) (read_result cx)) (\v2.
      bind (bind (eval_expr cx e3) (read_result cx)) (\v3 ee.
        (builtin_result cx ee.accounts ann bt (MAP expr_type [e1;e2;e3])
           [v1;v2;v3],ee))))
Proof
  strip_tac >> gvs[] >>
  simp[eval_expr_builtin_action, is_self_codesize_def, precompile_builtin_def,
       code_slice_source_def, builtin_args_length_ok_def] >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  simp[eval_exprs_cons_action, bind_assoc, bind_return]
QED

Theorem modular_reached_uint256_mods:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  expr_type e = BaseT (UintT 256) /\
  expr_body_pre_mods mods cenv cx env e st /\
  body_const_cells_agree_mods mods cx env st /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := obs) = (INL v,mid) ==>
  body_exprs_full_ok_mods mods exps cx rest /\
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid /\
  v = IntV (&w2n (val_to_w256 v))
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (st with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (st with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  simp[] >> conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
      qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
      simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
      qpat_x_assum `_ ==> body_exprs_full_ok_mods mods exps cx rest` irule >>
      rpt (goal_assum (drule_at Any))) >>
  irule uint_value_word_rep >> qexists_tac `256` >>
  gvs[value_runtime_typed_def, vyperValueTheory.evaluate_type_def]
QED
