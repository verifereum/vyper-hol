(* Delayed unwrap at the actual local Assign store cut. *)
Theory bodyAssignLocalRawOperandAtStoreMods
Ancestors
  bodyAssignLocalPreStoreMods bodyQualifiedPlaceTargetEntryMods
  bodyAssignQualifiedStageJoinMods bodyAssignLocalPlaceRoutesMods
  stmtLoweringMono exprLoweringProps fragExec compileEnv

Theorem raw_local_store_interval[local]:
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb (SOME vv)
    sr st shadow_sr shadow_st dst /\
  dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?op cur. unwrap_value cenv vv st = (op,cur) /\
    compile_assign_value cenv (FST dst) LocMemory op (is_word_type dty)
      (vv_location vv) dty (lowered_value_type cenv e)
      (type_memory_bytes cenv dty) cur = ((),sb) /\
    fn_has_code st cur func
Proof
  strip_tac >> drule_all_then strip_assume_tac qualified_place_code_intervals_mods >>
  qhdtm_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  Cases_on `unwrap_value cenv vv st` >>
  rename1 `unwrap_value cenv vv st = (op,cur)` >>
  `assign_place_store_code_mods cenv e (SOME vv) dst =
    comp_bind (unwrap_value cenv vv) (\op. compile_assign_value cenv
      (FST dst) LocMemory op (is_word_type dty) (vv_location vv) dty
      (lowered_value_type cenv e) (type_memory_bytes cenv dty))` by
    (qpat_assum `dst = (_,SOME LocMemory,_)` (once_rewrite_tac o single) >>
     simp[assign_place_memory_store_code_mods]) >>
  qpat_x_assum `assign_place_store_code_mods cenv e (SOME vv) dst st = _` mp_tac >>
  simp[comp_bind_def] >> strip_tac >> simp[] >>
  `cs_extends st cur` by
    (qspecl_then [`cenv`,`vv`,`st`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `cs_extends cur sb` by
    (`ci_mono cur (SND (compile_assign_value cenv (FST dst) LocMemory op
        (is_word_type dty) (vv_location vv) dty (lowered_value_type cenv e)
        (type_memory_bytes cenv dty) cur))` by SIMP_TAC (srw_ss()) [ci_mono_stmt_helpers] >>
     pop_assum mp_tac >> simp[ci_mono_def]) >>
  qpat_assum `fn_has_code st sb func`
    (mp_then (Pat `fn_has_code _ _ _`) mp_tac fn_has_code_split) >>
  disch_then (qspec_then `cur` mp_tac) >> simp[]
QED
