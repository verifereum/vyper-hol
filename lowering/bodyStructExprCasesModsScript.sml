(* Structural cases for the ranked linked evaluator induction. *)
Theory bodyStructExprCasesMods
Ancestors
  bodyStructFieldsCaseMods bodyAttributeCaseMods bodyPopCaseMods
  bodySubscriptCaseMods bodyIfExpInputsMods bodyIfExpSelectionMods
  exprSimIfExpCompat exprSimIfExpWidenedArm exprSimSource typedMemoryCopy
  exprBodyPreProps exprBodyPreTypingProps bodyInvCodeProps logArgumentTypeEval
  vyperTypeEvalProofs vyperTypeEvalCaseProofs vyperTypeInvariants allocLimits
  vyperTypeSystem exprLowering exprSimHypsDefs vyperAST loweringPosts
  bodyFullPredsMods context
Libs
  monadsyntax

Theorem body_structlit_case_full_mods:
  ^(concl bodyStructFieldsCaseModsTheory.body_structlit_case_full_mods)
Proof
  ACCEPT_TAC bodyStructFieldsCaseModsTheory.body_structlit_case_full_mods
QED

Theorem body_attribute_case_full_mods:
  ^(concl bodyAttributeCaseModsTheory.body_attribute_case_full_mods)
Proof
  ACCEPT_TAC bodyAttributeCaseModsTheory.body_attribute_case_full_mods
QED

Theorem body_pop_case_full_mods:
  ^(concl bodyPopCaseModsTheory.body_pop_case_full_mods)
Proof
  ACCEPT_TAC bodyPopCaseModsTheory.body_pop_case_full_mods
QED

Theorem body_subscript_case_full_mods:
  ^(concl bodySubscriptCaseModsTheory.body_subscript_case_full_mods)
Proof
  ACCEPT_TAC bodySubscriptCaseModsTheory.body_subscript_case_full_mods
QED

Triviality ifexp_arm_intcall_type_mods:
  expr_body_pre_mods mods ce cx env (Call t (IntCall fid) args drv) es ==>
  type_widens_to (get_tenv cx) (lowered_value_type ce (Call t (IntCall fid) args drv)) t /\
  (?stv. evaluate_type (get_tenv cx)
     (lowered_value_type ce (Call t (IntCall fid) args drv)) = SOME stv)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  PairCases_on `fid` >> fs[Once well_typed_expr_def] >>
  drule_all_then assume_tac expr_sim_inv_mods_return_type >>
  simp[lowered_value_type_def] >>
  rename1 `FLOOKUP env.fn_sigs (src,nm) = SOME sg` >>
  `fn_sigs_consistent env.fn_sigs cx` by
    fs[env_consistent_def,env_context_consistent_def] >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  pure_rewrite_tac[fn_sigs_consistent_def] >>
  disch_then (drule_then strip_assume_tac) >>
  `IS_SOME (FLOOKUP env.fn_sigs (src,nm))` by simp[] >>
  drule_all_then strip_assume_tac callable_body_typing_from_env_consistent >>
  gvs[] >> metis_tac[]
QED

Triviality ifexp_arm_kind_mods:
  expr_body_pre_mods mods ce cx env e es ==>
  (is_word_type (post_value_type ce e) ==> is_word_type (expr_type e)) /\
  (is_word_type (expr_type e) \/
   post_value_type ce e = expr_type e /\
     (same_memory_layout ce (lowered_value_type ce e) (expr_type e) \/
      is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e)) \/
   post_value_type ce e = lowered_value_type ce e /\
     type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
     (?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv))
Proof
  strip_tac >> Cases_on `is_word_type (expr_type e)` >> simp[] >>
  Cases_on `?ann fid args drv. e = Call ann (IntCall fid) args drv`
  >- (gvs[] >> drule_then strip_assume_tac ifexp_arm_intcall_type_mods >>
      fs[expr_type_def] >> Cases_on `is_bytestring_type ann`
      >- (simp[post_value_type_def] >>
          metis_tac[typed_copy_bytestring_source,type_widens_to_def,
                    CONJUNCT1 arg_type_fits_refl]) >>
      simp[post_value_type_def] >> metis_tac[return_source_word_widens_eq]) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_not_int_call] >>
  simp[] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >> simp[well_formed_type_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     simp[]) >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
    ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all ifexp_lowered_type_classify >>
  disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- simp[same_memory_layout_def,punnable_reflexive]
  >- simp[] >> metis_tac[]
QED

Theorem body_ifexp_case_full_mods:
  !mods exps cx t c a b.
    (!s raw s'. eval_expr cx c s = (INL raw,s') ==> body_expr_full_ok_mods mods exps cx a) /\
    (!s raw s'. eval_expr cx c s = (INL raw,s') ==> body_expr_full_ok_mods mods exps cx b) /\
    body_expr_full_ok_mods mods exps cx c ==>
    body_expr_full_ok_mods mods exps cx (IfExp t c a b)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_full_ok_mods_def] >>
  reverse conj_tac
  >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `?rty. evaluate_type (get_tenv cx) t = SOME rty` by
    (qpat_assum `well_typed_expr _ (IfExp _ _ _ _)`
       (strip_assume_tac o REWRITE_RULE [Once well_typed_expr_def]) >>
     simp[GSYM optionTheory.IS_SOME_EXISTS,GSYM well_formed_type_def] >>
     metis_tac[]) >>
  drule_then strip_assume_tac ifexp_body_pre_children_mods >>
  `!e. e = a \/ e = b ==>
    (is_word_type (post_value_type cenv e) ==> is_word_type t) /\
    (is_word_type t \/
     post_value_type cenv e = t /\
       (same_memory_layout cenv (lowered_value_type cenv e) t \/
        is_bytestring_type t /\ is_bytestring_type (lowered_value_type cenv e) /\
        arg_type_fits (lowered_value_type cenv e) t) \/
     post_value_type cenv e = lowered_value_type cenv e /\
       type_widens_to (get_tenv cx) (lowered_value_type cenv e) t /\
       (?stv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv))` by
    (gen_tac >> disch_tac >>
     qpat_assum `!es'. expr_sim_inv_mods _ _ _ _ es' ==> _`
       (qspec_then `es` mp_tac) >> simp[] >> strip_tac >>
     `expr_body_pre_mods mods cenv cx env e es /\ expr_type e = t` by
       (qpat_assum `e = a \/ e = b` (DISJ_CASES_THEN SUBST1_TAC) >> simp[]) >>
     qpat_assum `expr_body_pre_mods mods cenv cx env e es`
       (mp_then Any mp_tac ifexp_arm_kind_mods) >> simp[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    drule_then ACCEPT_TAC contract_inv_acyclic_struct_metadata >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
    type_memory_bytes cenv ty' = type_memory_size tvt` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `get_tenv cx` >> simp[] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!name fields. FLOOKUP _ name = SOME fields ==> _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `type_alloc_ok cenv t` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (IfExp _ _ _ _) _`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def,alloc_limits_expr_def]) >>
     first_assum ACCEPT_TAC) >>
  `~is_word_type t ==> type_memory_size rty < 2 ** 64` by
    (qpat_assum `!tt tv. evaluate_type _ tt = SOME tv ==> _`
       (drule_then (SUBST1_TAC o SYM)) >>
     qpat_assum `type_alloc_ok _ _` (ACCEPT_TAC o REWRITE_RULE [type_alloc_ok_def])) >>
  once_rewrite_tac[CONJ_COMM] >> irule ifexp_selection_full_mods >>
  drule_all_then (strip_assume_tac o SIMP_RULE bool_ss [FORALL_AND_THM,IMP_CONJ_THM])
    ifexp_arm_inputs_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qexistsl_tac [`env`,`mods`,`rty`] >>
      reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_tac >>
      ntac 4 (conj_tac >- (first_assum irule >> goal_assum (drule_at Any))) >>
      conj_tac
      >- (qpat_assum `!gs v ee. bind _ _ _ = _ ==> !e gs' raw mid. _ ==> eval_result_typed _ _ _`
            (drule_then ACCEPT_TAC)) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!gs v ee. bind _ _ _ = _ ==> !e gs' u mid rt. _ ==> value_has_type rt u`
        (drule_then (drule_all_then assume_tac)) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> disch_tac >>
      qpat_assum `!gs v ee. bind _ _ _ = _ ==> !e gs' u mid rt.
                  _ /\ evaluate_type _ _ = SOME rt /\ _ ==>
                  !pt. evaluate_type _ _ = SOME pt ==> value_has_type pt u`
        (drule_then (drule_all_then ACCEPT_TAC))) >>
  simp[]
QED
