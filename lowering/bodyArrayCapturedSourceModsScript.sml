(* Typing and popped-history facts for a fixed array returned by Pop. *)
Theory bodyArrayCapturedSourceMods
Ancestors vyperTypeInvariants[qualified,ignore_grammar] option[qualified,ignore_grammar]
  bodyArrayNoCopySourceMods bodyArrayNoCopyCutsMods
  bodySubscriptArrayRouteDefsMods bodyFullPredsMods bodyFullPostsMods
  exprBodyPreProps exprBodyPreTypingProps exprSimSubscriptArraySource
  exprSimSource exprSimHypsDefs vyperTypeEvalSoundness
  vyperInterpreter vyperState vyperAST vyperTypeSystem vyperTypeValues
  vyperTyping vyperPlaceTyping vyperEvalExprPreservesScopesDom
  vyperLookupStorageScopes vyperLookupStorage vyperArray
  compileEnv exprLowering context list
  vyperTypeEnv vyperTypeEnvPreservation vyperPlaceStatePreservation

Theorem captured_memory_read_type[local]:
  state_well_typed ee /\ popped_keys_indexed ee.scopes /\
  runtime_place_typed cx ee (MemoryPlace id path) tv /\
  read_result cx (PlaceR (MemoryPlace id path)) ee = (INL v,ee) ==>
  value_has_type tv v
Proof
  simp[runtime_place_typed_memory, vyperTypeInvariantsTheory.state_well_typed_def] >>
  rpt strip_tac >>
  drule_all_then strip_assume_tac scope_well_typed_lookup_scopes >>
  `read_memory_path entry path = INL v` by
    (qpat_x_assum `read_result _ _ _ = _` mp_tac >>
     simp[read_result_def, read_place_def, bind_def, get_scopes_def,
          lift_option_type_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `read_memory_path entry path` >> simp[return_def,raise_def]) >>
  Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (gvs[read_memory_path_def] >> irule evaluate_subscripts_type >>
      goal_assum (drule_at (Pat `evaluate_subscripts _ _ _ = _`)) >> simp[]) >>
  `read_popped entry.type path entry.popped = SOME v` by
    (gvs[read_memory_path_def, AllCaseEqs()]) >>
  `popped_history_typed entry.type entry.popped` by
    (drule lookup_scopes_EL >> strip_tac >>
     gvs[popped_keys_indexed_def, EVERY_EL] >>
     first_x_assum drule >> disch_then drule >> simp[]) >>
  irule read_popped_type >>
  goal_assum (drule_at (Pat `read_popped _ _ _ = _`)) >> simp[]
QED

Theorem array_captured_source_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et (Fixed n) /\
  ~subscript_reads_base cx obj idx /\
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et (Fixed n) st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  raw = PlaceR (MemoryPlace id path) /\ base_from_pop obj ==>
  ?etv. evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
    runtime_place_typed cx mid (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
    (!v. read_result cx raw mid = (INL v,mid) ==>
      value_has_type (ArrayTV etv (Fixed n)) v) /\
    popped_keys_indexed fin.scopes /\
    (!entry ty'. lookup_scopes id mid.scopes = SOME entry /\
      cenv.ce_var_type id = SOME ty' ==>
      evaluate_type (get_tenv cx) ty' = SOME entry.type)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac array_nocopy_base_inputs_mods >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid) /\
   bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin)` by
    (qhdtm_assum `array_nocopy_cut_mods`
       (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >> asm_rewrite_tac[]) >>
  `state_well_typed es /\ env_consistent env cx es /\ accounts_well_typed es.accounts /\
   context_well_typed cx /\ functions_well_typed cx /\ popped_keys_indexed es.scopes /\
   (!id t. FLOOKUP env.var_types id = SOME t ==> cenv.ce_var_type id = SOME t)` by
    (qhdtm_assum `expr_sim_inv_mods`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> asm_rewrite_tac[]) >>
  `state_well_typed mid /\ env_consistent env cx mid /\
   eval_result_typed (env,cx,mid) raw (Type (expr_type obj))` by
    (qspecl_then [`cx`,`obj`] (mp_tac o CONJUNCT1)
       (cj 5 eval_scc_type_sound_mutual) >>
     disch_then (qspecl_then [`env`,`es with gas_obs := gs1`,
                                `INL raw`,`mid`] mp_tac) >> simp[]) >>
  `popped_keys_indexed mid.scopes` by
    (qspecl_then [`cx`,`obj`,`es with gas_obs := gs1`,`INL raw`,`mid`] mp_tac
      eval_expr_popped_keys_indexed >> simp[]) >>
  `popped_keys_indexed fin.scopes` by
    (qpat_assum `bind (eval_expr cx idx) _ _ = _`
       (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split) >>
     simp[] >> rpt strip_tac >>
     drule read_result_state >> disch_then SUBST_ALL_TAC >>
     irule eval_expr_popped_keys_indexed >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    drule_then ACCEPT_TAC vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  qhdtm_x_assum `eval_result_typed` mp_tac >>
  simp[vyperTypeInvariantsTheory.eval_result_typed_def] >> strip_tac >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
  rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  qexists `etv` >> simp[] >>
  qpat_x_assum `tv = ArrayTV etv (Fixed n)` SUBST_ALL_TAC >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `env_consistent env cx mid` mp_tac >>
      simp[vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_scopes_consistent_def] >> strip_tac >>
      `?t. FLOOKUP env.var_types id = SOME t` by
        (qpat_assum `!id entry. lookup_scopes id mid.scopes = SOME entry ==> IS_SOME _`
           (qspecl_then [`id`,`entry`] mp_tac) >> gvs[optionTheory.IS_SOME_EXISTS]) >>
      `cenv.ce_var_type id = SOME t` by simp[] >>
      `evaluate_type (get_tenv cx) t = SOME entry.type` by
        (qpat_assum `!id ty entry. FLOOKUP env.var_types id = SOME ty /\ _ ==> _`
           (qspecl_then [`id`,`t`,`entry`] mp_tac) >> simp[]) >>
      gvs[]) >>
  rpt strip_tac >> drule_all_then ACCEPT_TAC captured_memory_read_type
QED
