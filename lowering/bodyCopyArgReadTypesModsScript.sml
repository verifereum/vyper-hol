(* Source typing of the actual argument reads preceding a local copy. *)
Theory bodyCopyArgReadTypesMods
Ancestors
  exprSimHypsDefs exprBodyPreProps exprSimSource exprLowering exprSafeOperand
  vyperInterpreter vyperState vyperTypeExprSoundness vyperTypeInvariants vyperTypeSystem
  vyperTypeEvalStoragePreservation vyperEvalOutcomeSuffix
  vyperTypeEvalCaseProofs vyperTypeArgFits vyperTypeDefaults list

Theorem copy_arg_eval_preserves_inv_mods[local]:
  expr_sim_inv_mods mods ce cx env st /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (rr,fin) ==>
  expr_sim_inv_mods mods ce cx env fin
Proof
  strip_tac >>
  `runtime_consistent env cx st /\ functions_well_typed cx` by
    fs[expr_sim_inv_mods_def, runtime_consistent_def] >>
  drule_all_then assume_tac eval_expr_preserves_runtime_consistent >>
  `outcomes_accounts_typed fin.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule_then assume_tac (cj 5 eval_outcome_suffix_mutual) >>
     drule_then irule outcome_suffix_EVERY >>
     fs[expr_sim_inv_mods_def, outcomes_accounts_typed_def]) >>
  `IS_SOME fin.outcomes` by
    (drule_at (Pat `eval_expr _ _ _ = _`) eval_expr_outcomes_some >>
     fs[expr_sim_inv_mods_def]) >>
  `popped_keys_indexed fin.scopes` by
    (drule_at (Pat `eval_expr _ _ _ = _`) eval_expr_popped_keys_indexed >>
     fs[expr_sim_inv_mods_def]) >>
  fs[expr_sim_inv_mods_def, runtime_consistent_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem copy_arg_reads_cons[local]:
  eval_exprs cx (head::args) st = (INL vs,fin) ==>
  ?v mid tail raw.
    eval_expr cx head st = (INL raw,mid) /\
    read_result cx raw mid = (INL v,mid) /\
    eval_exprs cx args mid = (INL tail,fin) /\ vs = v::tail
Proof
  pure_once_rewrite_tac[evaluate_def] >>
  simp_tac std_ss [bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  drule_then SUBST_ALL_TAC read_result_state >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem copy_arg_read_types_from_members_mods:
  !args st vs fin.
    expr_sim_inv_mods mods ce cx env st /\
    EVERY (\e. well_typed_expr env e /\ alloc_limits_expr ce e /\
               call_evaluation_safe cx (int_calls_expr e)) args /\
    eval_exprs cx args st = (INL vs,fin) /\
    (!e s v t. MEM e args /\ expr_sim_inv_mods mods ce cx env s /\
      bind (eval_expr cx e) (read_result cx) s = (INL v,t) ==>
      value_runtime_typed env (lowered_value_type ce e) v) ==>
    LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs
Proof
  Induct >- simp[Once evaluate_def, return_def] >>
  pure_rewrite_tac[EVERY_DEF] >> rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac copy_arg_reads_cons >> gvs[] >>
  conj_tac
  >- (first_x_assum irule >> simp[] >>
      qexistsl_tac [`st`, `mid`] >> simp[bind_def]) >>
  `expr_sim_inv_mods mods ce cx env mid` by
    (drule_all copy_arg_eval_preserves_inv_mods >> simp[]) >>
  qpat_x_assum `!st vs fin. _` irule >>
  reverse conj_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* The physical layouts are witnessed by the already-typed values.  The
   annotation layouts follow from source typing; fitting is a separate static
   property of the lowering, not a consequence of one successful read. *)
Theorem copy_arg_read_layouts_mods:
  !args vs.
    env_consistent env cx st /\ EVERY (well_typed_expr env) args /\
    EVERY (\e. arg_type_fits (lowered_value_type ce e) (expr_type e)) args /\
    LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs ==>
    arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args) /\
    ?ptvs stvs.
      LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv)
        (MAP (lowered_value_type ce) args) ptvs /\
      LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv)
        (MAP expr_type args) stvs /\
      values_have_types ptvs vs
Proof
  Induct >> Cases_on `vs` >>
  simp[arg_types_fit_LIST_REL, values_have_types_LIST_REL] >>
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_type_defs_get_tenv] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
           well_formed_type env.type_defs ty` by
    (simp[well_formed_type_def] >> metis_tac[env_consistent_var_type_evaluates]) >>
  drule_all well_typed_expr_type_well_formed >>
  simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `stv` assume_tac) >>
  qpat_x_assum `value_runtime_typed _ _ _`
    (qx_choose_then `ptv` strip_assume_tac o REWRITE_RULE[value_runtime_typed_def]) >>
  first_x_assum drule_all >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`ptvs`, `stvs`] strip_assume_tac))
  >- fs[arg_types_fit_LIST_REL] >>
  qexistsl_tac [`ptv::ptvs`, `stv::stvs`] >>
  fs[values_have_types_LIST_REL] >> metis_tac[]
QED
