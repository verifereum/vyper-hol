(* Linked composition of a literal-membership operand run and its scalar tail. *)
Theory bodyMembershipLiteralMods
Ancestors
  bodyMembershipLiteralOperandsMods bodyMembershipLiteralSuffixMods bodyScalarStackVVMods
  bodyFullWordArgs exprSimBopInLiteralWord exprSimWordArgs exprWordOperand
  exprSimFullBundleProps exprBodyPreProps exprLoweringProps exprSimUnopProps
  gasShadow gasShadowState gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  fragExec compileEnv freshWrites vyperStorageTrace vyperTypeSystem vyperAST list
  bodyFullPostsMods exprSimDefs vyperStorageFootprint vyperState gasContext loweringPosts
  exprSimHypsDefs bodyFullPredsMods ptrDiscipline venomState loweringStateRelDefs
Libs monadsyntax

Triviality membership_literal_arg_facts:
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) ==>
  ann = BaseT BoolT /\ is_ArrayT a /\
  (?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv) /\
  wb_args_shape cenv expr_type (e1::elems)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac literal_membership_typing_mods >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  `well_formed_type env.type_defs a /\ well_typed_expr env e1 /\ well_typed_exprs env elems` by
    (qpat_x_assum `well_typed_expr _ (Builtin _ (Bop _) _)` mp_tac >>
     simp[well_typed_expr_def]) >>
  simp[is_ArrayT_def] >> conj_tac
  >- (qpat_x_assum `well_formed_type env.type_defs a` mp_tac >>
      simp[well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `evaluate_type (get_tenv cx) (expr_type e1)` >> simp[]) >>
  simp[wb_args_shape_def] >> rpt gen_tac >> strip_tac >>
  irule lower_value_word_shape >> simp[] >>
  `is_word_type (expr_type e) /\ well_typed_expr env e` by
    (fs[EVERY_MEM] >> metis_tac[constSubstCorrectTheory.frame_well_typed_exprs_member]) >>
  qpat_assum `lower_value _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `well_typed_expr env e` (irule_at Any) >> simp[] >>
  rpt strip_tac >> drule_all exprSimSourceTheory.env_consistent_var_type_evaluates >>
  simp[well_formed_type_def]
QED

Triviality membership_shadow_args:
  lower_word_args cenv expr_type args sa = (xs,sm) /\ gas_shadow_state sa shadow_sa ==>
  ?shadow_sm. lower_word_args (gas_shadow_env T cenv) expr_type
       (MAP gas_shadow_expr args) shadow_sa = (xs,shadow_sm) /\
     gas_shadow_state sm shadow_sm
Proof
  strip_tac >>
  `gas_shadow_compiles (lower_word_args cenv expr_type args)
     (lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr args))` by
    simp[gas_shadow_compiles_lower_word_args] >>
  pop_assum (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
  Cases_on `lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr args) shadow_sa` >>
  simp[]
QED

Triviality membership_tail_extends:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
    else compile_list_membership_notin needle xs) sm = (op,sb) ==>
  cs_extends sm sb
Proof
  Cases_on `bop = In` >> simp[] >> strip_tac >>
  metis_tac[literal_membership_straight, straight_fresh_cs_extends]
QED

Triviality membership_literal_code:
  (bop = In \/ bop = NotIn) /\ is_ArrayT a /\
  lower_value compile_expr cenv ty
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])) shadow_sa = (op,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb) ==>
  ?needle xs sm shadow_sm.
    lower_word_args cenv expr_type (e1::elems) sa = (needle::xs,sm) /\
    lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr (e1::elems))
      shadow_sa = (needle::xs,shadow_sm) /\
    (if bop = In then compile_list_membership_in needle xs
      else compile_list_membership_notin needle xs) sm = (op,sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sm,shadow_sa,shadow_sm) /\
    fn_has_code sm sb func
Proof
  rewrite_tac[expr_sim_full_code_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac literal_lower_value >>
  drule_all_then strip_assume_tac membership_shadow_args >>
  drule_all_then assume_tac membership_tail_extends >>
  `cs_extends shadow_sm shadow_sb` by suspend "shadow_tail" >>
  qexistsl_tac [`needle`,`xs`,`sm`,`shadow_sm`] >> simp[] >>
  qpat_assum `lower_word_args cenv _ _ _ = _`
    (strip_assume_tac o SRULE [ci_mono_def] o MATCH_MP (SPEC_ALL ci_mono_lower_word_args)) >>
  qpat_assum `lower_word_args (gas_shadow_env T _) _ _ _ = _`
    (strip_assume_tac o SRULE [ci_mono_def] o MATCH_MP (SPEC_ALL ci_mono_lower_word_args)) >>
  rpt conj_tac >> irule fn_has_code_mid >> simp[]
  >- (qexistsl_tac [`sb`,`sa`] >> simp[cs_extends_refl])
  >- (qexistsl_tac [`shadow_sb`,`shadow_sa`] >> simp[cs_extends_refl]) >>
  qexistsl_tac [`sb`,`sa`] >> simp[cs_extends_refl]
QED

Resume membership_literal_code[shadow_tail]:
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[NoAsms, gas_shadow_expr_def, gas_shadow_builtin_def] >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) shadow_sa = _`
    (mp_then (Pat `lower_value _ _ _ _ _ = _`) mp_tac literal_lower_value) >>
  impl_tac >- simp[] >> strip_tac >> gvs[] >>
  metis_tac[literal_membership_straight, straight_fresh_cs_extends]
QED

Finalise membership_literal_code

Theorem membership_literal_value_mods:
  !DF lo d PG mods exps src tops ctx shadow_ctx func shadow_func
    cenv cx env ty ann bop e1 a t n elems es.
    (bop = In \/ bop = NotIn) /\
    is_word_type (expr_type e1) /\
    body_expr_full_ok_mods mods exps cx e1 /\
    ((?s raw s' s1 v s1'. eval_expr cx e1 s = (INL raw,s') /\
        read_result cx raw s1 = (INL v,s1')) ==>
      body_expr_full_ok_mods mods exps cx (Builtin a (MakeArray t n) elems)) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es ==>
    expr_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac membership_literal_arg_facts >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  drule_all_then strip_assume_tac membership_literal_code >>
  drule_all_then strip_assume_tac lower_word_args_shape_ready >>
  `EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs)` by
    (qpat_assum `EVERY (\x. _ /\ (!l. x <> Label l)) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all bop_in_literal_operands_mods >>
  disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ PrefixPost PrefixExit` >>
  drule_all_then (fn th => rewrite_tac[th]) literal_membership_action_flat_mods >>
  simp[expr_type_def, is_word_type_def] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_values >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame (return _)`]
  >- simp[storage_trace_frame_return] >>
  qexists_tac `\H res ee G tn u. PrefixPost H res ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac >- suspend "prefix" >> suspend "suffix"
QED

Resume membership_literal_value_mods[prefix]:
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ PrefixPost PrefixExit` (irule_at Any) >>
  BETA_TAC >> conj_tac >- simp[] >>
  simp[Abbr `PrefixExit`] >> rpt gen_tac >> Cases_on `res` >>
  simp[expr_exit_INL, halt_exit_def] >>
  rpt strip_tac >>
  qpat_assum `expr_exit (INR _ : value list + exception) _` mp_tac >>
  pure_once_rewrite_tac[INST_TYPE [alpha |-> ``:value list``, beta |-> ``:value``]
    stmtSimPropsTheory.expr_exit_INR_type] >> simp[]
QED

Resume membership_literal_value_mods[suffix]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`s1`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `PrefixPost` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `?vs. res = INL vs /\ _` strip_assume_tac >>
  Cases_on `vs` >- gvs[] >>
  rename1 `LIST_REL _ (needle::xs) (v::vs)` >>
  `res = INL (v::vs)` by fs[] >>
  qpat_x_assum `res = INL (v::vs)` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v::vs` >> simp[] >>
  irule bop_in_literal_suffix_mods >>
  qpat_assum `(if _ then compile_list_membership_in _ _ else _) _ = _` (irule_at Any) >>
  qexistsl_tac [`tv`,`expr_type e1`] >> simp[] >>
  `(mid with gas_obs := []) = mid` by simp[evaluation_state_component_equality] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  gvs[]
QED

Finalise membership_literal_value_mods

(* The ranked expression clause also needs the unforced StackValue judgment. *)
Theorem membership_literal_sim_mods:
  (bop = In \/ bop = NotIn) /\
  is_word_type (expr_type e1) /\
  body_expr_full_ok_mods mods exps cx e1 /\
  ((?s raw s' s1 v s1'. eval_expr cx e1 s = (INL raw,s') /\
      read_result cx raw s1 = (INL v,s1')) ==>
    body_expr_full_ok_mods mods exps cx (Builtin a (MakeArray t n) elems)) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_asm1_tac
  >- (irule membership_literal_value_mods >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `body_const_cells_agree_mods _ _ _ _` (irule_at Any) >>
      qexists_tac `exps` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac literal_membership_typing_mods >>
  irule scalar_stack_vv_sim_full_mods >> simp[expr_type_def, is_word_type_def] >>
  simp[exprSimOperatorsTheory.compile_bop_stack] >>
  rpt strip_tac >> drule_then ACCEPT_TAC eval_expr_builtin_value
QED
