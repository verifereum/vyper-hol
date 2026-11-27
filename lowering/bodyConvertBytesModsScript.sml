(* Linked bytestring Convert: compose the forced operand with its selected suffix. *)
Theory bodyConvertBytesMods
Ancestors
  bodyConvertBytesEntryMods bodyConvertBytesReadMods bodyConvertBytesBindMods
  bodyConvertBytesChildStageMods bodyConvertBytesSuffixMods
  bodyConvertBytesCastLandingMods bodyConvertBytesWidenLandingMods
  bodyFullPredsMods bodyFullPostsMods exprBodyPreProps exprSimHyps exprSimStack
  exprLoweringProps exprSimConvertBytes exprSimConvert typeLayoutProps exprSimHypsDefs allocLimits
  vyperTypeEvalCaseProofs vyperTypeSystem vyperAST compileEnv context
Libs monadsyntax

Theorem convert_bytes_route_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok_mods mods exps cx e /\ is_bytestring_type dst ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (TypeBuiltin ann Convert dst [e]) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (TypeBuiltin ann Convert dst [e]) es /\
  (!sa. ?out sb. compile_expr ce ty (TypeBuiltin ann Convert dst [e]) sa =
    (LocatedValue dst (mk_ptr out LocMemory),sb)) /\
  (!s raw mid. eval_expr cx (TypeBuiltin ann Convert dst [e]) s = (INL raw,mid) ==>
    ?v. raw = Value v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac bodyConvertBytesEntryModsTheory.bytes_convert_entry_mods >>
  qpat_x_assum `ann = dst` SUBST_ALL_TAC >>
  `!sa. ?out sb. compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
     (LocatedValue dst (mk_ptr out LocMemory),sb)` by
    (irule bodyConvertBytesEntryModsTheory.bytes_convert_memory_shape_mods >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx ty (TypeBuiltin dst Convert dst [e]) es` by suspend "vv" >>
  (conj_tac >- (irule bytes_convert_read_mods >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC eval_expr_type_builtin_value
QED

Resume convert_bytes_route_mods[vv]:
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ _`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!a b c d e f g h i j k l m n. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (irule o cj 2 o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
     asm_rewrite_tac[] >>
     (conj_tac >- (qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC)) >>
     qexists_tac `env` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_body_pre_mods_inv >>
     disch_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
     drule_then ACCEPT_TAC env_consistent_type_defs_get_tenv) >>
  `?tout. evaluate_type (get_tenv cx) dst = SOME tout` by
    fs[well_formed_type_def,optionTheory.IS_SOME_EXISTS] >>
  `type_memory_bytes ce dst = type_memory_size tout` by
    (Cases_on `dst` >> fs[is_bytestring_type_def] >>
     irule type_memory_bytes_base_evaluated >> goal_assum (drule_at Any)) >>
  `type_alloc_ok ce dst` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `e` |-> `TypeBuiltin dst Convert dst [e]`]
        (SPEC_ALL alloc_limits_expr_type_alloc_ok)) >>
     simp[expr_type_def] >> disch_then irule >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (TypeBuiltin _ _ _ _) _`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  `type_alloc_ok ce (expr_type e)` by
    (irule alloc_limits_expr_type_alloc_ok >>
     qpat_assum `expr_body_pre_mods _ _ _ _ e _`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[expr_vv_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`op`,`sm`,`shm`,`out`] (map_every assume_tac o CONJUNCTS))
    bodyConvertBytesEntryModsTheory.bytes_convert_paired_cut_mods >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_assum `lower_value _ ce _ e sa = (op,sm)`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  irule bytes_convert_bind_mods >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`op`,`sm`] >>
  (reverse conj_tac >- (irule convert_bytes_child_stage >>
     asm_rewrite_tac[] >>
     (conj_tac >- (qexists_tac `dst` >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- (qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC)) >>
     qexistsl_tac [`shadow_sa`,`shadow_func`,`shm`] >> asm_rewrite_tac[])) >>
  suspend "suffix"
QED

Resume convert_bytes_route_mods[suffix]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (\H res ee G tn t. _) _ _ _ _ _ _`
    (assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11, UNWIND_THM2]) >>
  Cases_on `type_memory_bytes ce (lowered_value_type ce e) < type_memory_bytes ce dst` >>
  qpat_x_assum `(if _ then _ else _)` mp_tac >> asm_rewrite_tac[] >> strip_tac
  >- suspend "widen" >>
  suspend "cast"
QED

Resume convert_bytes_route_mods[widen]:
  irule bytes_convert_suffix_continuation_mods >>
  asm_rewrite_tac[] >> strip_tac >> BETA_TAC >> disj1_tac >>
  irule (BETA_RULE bytes_convert_widen_landing_mods) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qexists_tac `tout` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  (conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qexistsl_tac [`op`,`sm`] >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[]))) >>
  (conj_tac >- (qexists_tac `storage_trace_horizon mid.storage_trace` >> first_assum ACCEPT_TAC)) >>
  qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC
QED

Resume convert_bytes_route_mods[cast]:
  `type_memory_bytes ce dst <= type_memory_bytes ce (lowered_value_type ce e)` by decide_tac >>
  qpat_assum `compile_type_convert _ _ sm = (out,sb)`
    (mp_then (Pat `compile_type_convert _ _ _ = _`) mp_tac
      convert_bytestring_suffix_grows) >>
  asm_rewrite_tac[] >> strip_tac >>
  irule bytes_convert_cast_landing_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qexists_tac `tout` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`op`,`sm`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise convert_bytes_route_mods
