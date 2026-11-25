Theory createCtorSourceReadinessMods
Ancestors
  createCtorMaterializePhysicalMods exprBodyPreProps exprSimHypsDefs
  exprSimHyps exprSimSource exprSimIfExpCompat exprSimWordArgs
  abiEncodeArgsCase typedMemoryCopy valueEncodingTyping
  vyperTypeEvalCaseProofs vyperTypeSystem vyperState vyperAST
  allocLimits compileEnv exprLowering arithmetic words finite_map
Libs monadsyntax

Theorem ctor_source_lowered_fits_mods[local]:
  expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e ==>
  arg_type_fits (lowered_value_type ce e) (expr_type e)
Proof
  strip_tac >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
            ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (pop_assum strip_assume_tac >> gvs[] >> PairCases_on `fid` >>
      gvs[vyperTypeSystemTheory.well_typed_expr_def, lowered_value_type_def,
          vyperASTTheory.expr_type_def] >>
      first_x_assum (drule_then SUBST1_TAC) >>
      fs[vyperTypeSystemTheory.type_widens_to_def]) >>
  `env_consistent env cx es` by metis_tac[expr_sim_inv_mods_env] >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_type_defs_get_tenv] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[env_consistent_var_type_evaluates, well_formed_type_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[expr_sim_inv_mods_def] >>
  drule_all ifexp_lowered_type_classify >> strip_tac >>
  gvs[ifexp_arg_type_fits_refl]
QED

Theorem ctor_source_readiness_mods:
  expr_body_pre_mods mods ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\
         val_wf tv v /\
         type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
         type_memory_size tv < 2 ** 64 /\
         type_memory_size tv + 64 < dimword (:256))
Proof
  strip_tac >> conj_tac
  >- (drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  strip_tac >>
  `(vyperState$bind (eval_expr cx e) (read_result cx)) es = (INL v,es')` by
    (drule exprSimSourceTheory.eval_expr_read_INL >>
     strip_tac >> simp[vyperStateTheory.bind_def]) >>
  drule_all ctor_physical_bound_read_type_mods >>
  disch_then (qx_choose_then `tv` strip_assume_tac) >>
  `expr_sim_inv_mods mods ce cx env es` by metis_tac[expr_body_pre_mods_inv] >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[ctor_source_lowered_fits_mods, expr_body_pre_mods_well_typed] >>
  `type_memory_bytes ce (lowered_value_type ce e) <=
     type_memory_bytes ce (expr_type e)` by
    metis_tac[abi_args_fits_memory_bytes] >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    (`alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def]) >>
  qexists_tac `tv` >> simp[valueEncodingTypingTheory.value_has_type_val_wf] >>
  fs[wordsTheory.dimword_def] >> decide_tac
QED
