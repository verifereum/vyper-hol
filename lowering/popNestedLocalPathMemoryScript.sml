(* Source path typing for successful local target evaluation. *)
Theory popNestedLocalPathMemory
Ancestors
  popNestedLocalTypeMemory targetPlaceSim targetPlaceSimCasesBase exprSimHypsDefs
  vyperTypeEvalSoundness
  vyperPlaceTyping vyperPlaceResultTyping vyperPlaceStatePreservation
  exprSimSubscriptArrayOrigin allocLimits list rich_list vyperState vyperTypeInvariants
  vyperInterpreter vyperValue option

Theorem pop_nested_local_path_typed:
  target_pre cenv cx env bt st /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL (PlaceR (MemoryPlace id path)),fin) ==>
  ?entry tv. lookup_scopes id fin.scopes = SOME entry /\
    evaluate_type env.type_defs ty = SOME tv /\
    subscripts_type entry.type path = SOME tv
Proof
  strip_tac >>
  `env_consistent env cx st /\ state_well_typed st /\
   context_well_typed cx /\ accounts_well_typed st.accounts /\
   functions_well_typed cx` by fs[target_pre_def, expr_sim_inv_def] >>
  drule_all (cj 1 (cj 7 eval_scc_type_sound_results_mutual)) >>
  simp[eval_result_typed_place, runtime_place_typed_memory] >> metis_tac[]
QED

Theorem local_path_fixed_snoc[local]:
  !path tv sb.
  (!prefix i suffix et n.
    path = prefix ++ ValueSubscript (IntV i)::suffix ==>
    subscripts_type tv prefix <> SOME (ArrayTV et (Dynamic n))) /\
  (!i et n. sb = ValueSubscript (IntV i) ==>
    subscripts_type tv path <> SOME (ArrayTV et (Dynamic n))) ==>
  !prefix i suffix et n.
    path ++ [sb] = prefix ++ ValueSubscript (IntV i)::suffix ==>
    subscripts_type tv prefix <> SOME (ArrayTV et (Dynamic n))
Proof
  Induct >> rpt gen_tac
  >- (strip_tac >> rpt gen_tac >> Cases_on `prefix` >> simp[] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >> rpt gen_tac >> Cases_on `prefix`
  >- (simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!prefix i suffix et n. h::path = _ ==> _`
        (qspecl_then [`[]`, `i`, `path`, `et`, `n`] mp_tac) >> simp[]) >>
  simp[] >> strip_tac >> qpat_x_assum `h = h'` (SUBST_ALL_TAC o SYM) >>
  Cases_on `subscript_type tv h` >> simp[subscripts_type_def] >>
  qpat_x_assum `!tv sb. _` irule >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!prefix i suffix et n. h::path = _ ==> _`
        (qspecl_then [`h::prefix`, `i'`, `suffix'`, `et`, `n`] mp_tac) >>
      simp[subscripts_type_def]) >>
  qexistsl_tac [`i`, `sb`, `suffix`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!i et n. sb = _ ==> _` drule >> simp[subscripts_type_def]
QED

Theorem local_entry_type_agrees[local]:
  env_consistent env cx s /\ env_consistent env cx t /\
  lookup_scopes id s.scopes = SOME entry /\
  lookup_scopes id t.scopes = SOME other ==>
  entry.type = other.type
Proof
  simp[env_consistent_def, env_scopes_consistent_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
  qpat_x_assum `!id entry. lookup_scopes id s.scopes = _ ==> _` drule >>
  strip_tac >>
  qpat_x_assum `!id ty entry. _ /\ lookup_scopes id s.scopes = _ ==> _`
    drule_all >>
  qpat_x_assum `!id ty entry. _ /\ lookup_scopes id t.scopes = _ ==> _`
    drule_all >> simp[]
QED
