(* Linked typing and source cuts for Concat, before its allocation prefix. *)
Theory bodyConcatStaticMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimHyps exprSimSource
  supportedExprTraverse supportedProgram allocLimits compileEnv constSubstCorrect
  exprSimHypsDefs
  vyperTypeSystem vyperTypeInvariants vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperContext vyperInterpreter vyperState vyperAST vyperValue list
Libs monadsyntax

Theorem concat_child_pre_mods[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann (Concat n) args) es /\
  MEM e args /\ expr_sim_inv_mods mods cenv cx env mid ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
  rw[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
     supported_exprs_exists_every, EXISTS_MEM] >>
  gvs[expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem,
            int_calls_exprs_every_mem]
QED

Theorem concat_arg_class[local]:
  ((EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
   (EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))) ==>
  EVERY (\e. is_bytestring_type (expr_type e) \/
             ?m. expr_type e = BaseT (BytesT (Fixed m))) args
Proof
  simp[EVERY_MAP, EVERY_MEM] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[is_bytestring_type_def] >>
  Cases_on `bd` >> simp[is_bytestring_type_def]
QED

Theorem concat_static_mods:
  expr_body_pre_mods mods cenv cx env (Builtin a (Concat n) args) es /\
  (builtin_args_length_ok (Concat n) (LENGTH args) ==>
   body_exprs_full_ok_mods mods exps cx args) ==>
  body_exprs_full_ok_mods mods exps cx args /\
  (!e ee. MEM e args /\ expr_sim_inv_mods mods cenv cx env ee ==>
     expr_body_pre_mods mods cenv cx env e ee) /\
  expr_sim_inv_mods mods cenv cx env es /\
  2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
  ((a = BaseT (BytesT (Dynamic n)) /\
    EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
   (a = BaseT (StringT n) /\
    EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))) /\
  (?tvr. evaluate_type (get_tenv cx) a = SOME tvr) /\
  EVERY (\e. is_bytestring_type (expr_type e) \/
             ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
  concat_alloc_size (MAP expr_type args) < 2 ** 64 /\
  32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <=
    concat_alloc_size (MAP expr_type args) /\
  32 + concat_data_bound 0 (MAP expr_type args) <= concat_alloc_size (MAP expr_type args) /\
  eval_expr cx (Builtin a (Concat n) args) =
    bind (eval_exprs cx args) (\vs st.
      ((case evaluate_concat n vs of INL v => INL (Value v)
                                  | INR err => INR (Error err)), st))
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >> simp[env_consistent_def, env_context_consistent_def]) >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    (qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_mods_def, alloc_limits_expr_def]) >>
  pure_asm_rewrite_tac[concat_alloc_size_bounds] >> rpt conj_tac
  >- (first_x_assum irule >> simp[builtin_args_length_ok_def])
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC concat_child_pre_mods)
  >- (qpat_x_assum `well_formed_type _ _` mp_tac >>
      simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS])
  >- (irule concat_arg_class >> metis_tac[])
  >- (qpat_assum `concat_alloc_size _ < _` (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])) >>
  qspec_then `MAP expr_type args` (strip_assume_tac o SIMP_RULE (srw_ss()) [])
    concat_alloc_size_bounds >>
  simp[eval_expr_concat_bind]
QED
