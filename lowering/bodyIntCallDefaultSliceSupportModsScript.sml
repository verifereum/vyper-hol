Theory bodyIntCallDefaultSliceSupportMods
Ancestors
  alist list rich_list pair finite_map pred_set
  supportedExprs constSubstMods constSubstStmtsPreserve
  vyperTypeContract vyperTypeContractContext vyperTypeContractStaticMaps
  vyperTypeCallGraph vyperImportRefs vyperImportRefsProps
  whitelistLinkedBodyEnv whitelistLinkedBodyExprs whitelistCheckerFnSigs
  whitelistLinkedBodyTypes whitelistLinkedBodyData supportedProgram supportedDecls
  vyperState

Triviality slice_raw_support:
  supported_pure_exprs tops dflts ==>
  supported_pure_exprs tops (DROP n dflts)
Proof
  simp[supported_pure_exprs_every, EVERY_DROP]
QED

Triviality slice_imported_refs_drop:
  !n es. imported_exprs_refs_ok es ==> imported_exprs_refs_ok (DROP n es)
Proof
  Induct >> simp[] >> Cases >> simp[imported_expr_refs_ok_def]
QED

Triviality slice_imported_refs:
  check_contract mode layouts (addr:160 word) mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops ==>
  src = NONE \/ imported_exprs_refs_ok
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))
Proof
  Cases_on `src` >> simp[] >> strip_tac >>
  drule ALOOKUP_MEM >> strip_tac >>
  drule_all check_contract_subst_imported_function_refs_ok >>
  simp[slice_imported_refs_drop]
QED

Triviality slice_runtime_no_calls:
  (!e. runtime_constant_expr mods e ==> int_calls_expr e = []) /\
  (!es. EVERY (runtime_constant_expr mods) es ==> int_calls_exprs es = []) /\
  (!fs. EVERY (runtime_constant_expr mods) (MAP SND fs) ==> int_calls_named_exprs fs = [])
Proof
  `(!e. runtime_constant_expr mods e ==> int_calls_expr e = []) /\
   (!t:base_assignment_target. (\x. T) t) /\
   (!es. EVERY (runtime_constant_expr mods) es ==> int_calls_exprs es = []) /\
   (!opt:expr option. (\x. T) opt) /\
   (!fs. EVERY (runtime_constant_expr mods) (MAP SND fs) ==> int_calls_named_exprs fs = [])`
    suffices_by simp[] >>
  ho_match_mp_tac int_calls_expr_ind >>
  simp[runtime_constant_expr_def, int_calls_expr_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[SF ETA_ss] >>
  metis_tac[constant_expr_no_internal_calls]
QED

Triviality slice_without_call_signatures:
  EVERY (runtime_constant_expr mods) es /\ well_typed_exprs env es ==>
  well_typed_exprs (env with fn_sigs := FEMPTY) es
Proof
  strip_tac >> drule (cj 2 slice_runtime_no_calls) >> strip_tac >>
  mp_tac (Q.INST [`ks` |-> `{}`] (cj 4 well_typed_fn_sigs_restrict)) >>
  disch_then (qspecl_then [`env`, `es`] mp_tac) >>
  simp[DRESTRICT_IS_FEMPTY]
QED

Triviality slice_no_empty_main_struct:
  check_contract mode layouts (addr:160 word) mods = SOME art /\
  ALOOKUP mods NONE = SOME tops ==>
  !name. ~MEM (StructDecl name []) tops
Proof
  rpt strip_tac >> drule_all check_contract_toplevel_decl_MEM_checked >>
  simp[check_toplevel_decl_def]
QED

(* Only the data part of the checked environment is needed as an input here.
   The selected defaults cannot call, so retaining any call signature is
   unnecessary, including out-of-slice main signatures in deploy mode. *)
Triviality slice_supported_from_data:
  check_contract mode layouts (addr:160 word) mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  linked_body_data_env tops src (artifact_env art mods src) /\
  (!k t. FLOOKUP art.cta_bare_global_assignable k = SOME t ==>
         FLOOKUP art.cta_bare_globals k = SOME t) /\
  supported_pure_exprs tops dflts /\
  well_typed_exprs (artifact_env art mods src)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)) /\
  EVERY (runtime_constant_expr mods)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)) ==>
  supported_pure_exprs tops (DROP n dflts) /\
  supported_pure_exprs tops (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))
Proof
  strip_tac >> conj_tac >- simp[slice_raw_support] >>
  drule_all slice_imported_refs >> disch_then (qspec_then `n` assume_tac) >>
  drule_all linked_checked_body_type_facts >> strip_tac >>
  drule_all slice_without_call_signatures >> strip_tac >>
  qabbrev_tac `env = (artifact_env art mods src) with fn_sigs := FEMPTY` >>
  `linked_body_env tops src (type_env_all_modules mods) env` by
    (qpat_assum `linked_body_data_env _ _ _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [linked_body_data_env_def, artifact_env_def]) >>
     simp[Abbr `env`, artifact_env_def, linked_body_env_def,
          linked_body_data_env_def, linked_body_calls_env_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `src = NONE ==> !name. ~MEM (StructDecl name []) tops` by
    (strip_tac >> gvs[] >> drule_all slice_no_empty_main_struct >> simp[]) >>
  simp[supported_pure_exprs_every] >> drule linked_well_typed_expr_supported >>
  disch_then (qspec_then `type_env_all_modules mods` strip_assume_tac) >>
  first_x_assum irule >> simp[] >> qexists_tac `env` >> simp[]
QED

Triviality slice_main_slots:
  supported_program tops /\ MEM tl tops ==>
  case tl of
    VariableDecl _ Storage _ _ slot => IS_SOME slot
  | VariableDecl _ Transient _ _ slot => IS_SOME slot
  | HashMapDecl _ _ _ _ _ slot => IS_SOME slot
  | _ => T
Proof
  strip_tac >> drule_all supported_program_declaration >> strip_tac >>
  Cases_on `tl` >> fs[supported_declaration_header_def]
  >- (rename1 `MEM (VariableDecl _ m _ _ opt) _` >>
      Cases_on `m` >> Cases_on `opt` >> gvs[]) >>
  rename1 `MEM (HashMapDecl _ _ _ _ _ slot) _` >>
  Cases_on `slot` >> gvs[]
QED

Triviality slice_bare_assignable_consistent:
  check_contract mode layouts (addr:160 word) mods = SOME art ==>
  !k ty. FLOOKUP art.cta_bare_global_assignable k = SOME ty ==>
         FLOOKUP art.cta_bare_globals k = SOME ty
Proof
  strip_tac >> gen_tac >> PairCases_on `k` >> rpt strip_tac >>
  Cases_on `mode`
  >- (mp_tac (Q.INST [`sources` |-> `[(addr,mods)]`,
                      `tx` |-> `empty_call_txn with target := addr`]
               check_contract_bare_global_assignable_consistent_deploy) >>
      simp[] >> disch_then drule >> strip_tac >> simp[]) >>
  mp_tac (Q.INST [`sources` |-> `[(addr,mods)]`,
                  `tx` |-> `empty_call_txn with target := addr`]
            check_contract_bare_global_assignable_consistent_initial) >>
  simp[] >> disch_then drule >> strip_tac >> simp[]
QED

Theorem intcall_default_slice_support_mods:
  check_contract mode layouts (addr:160 word) mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  (src = NONE ==> supported_program tops) /\
  supported_pure_exprs tops dflts /\
  well_typed_exprs (artifact_env art mods src)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)) /\
  EVERY (runtime_constant_expr mods)
    (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts)) ==>
  supported_pure_exprs tops (DROP n dflts) /\
  supported_pure_exprs tops (DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts))
Proof
  strip_tac >>
  `linked_body_data_env tops src (artifact_env art mods src)` by
    (mp_tac (Q.INST [`env` |-> `artifact_env art mods src`]
       (INST_TYPE [``:'a`` |-> ``:160 word``] linked_checked_data_env_from_slots)) >>
     simp[artifact_env_def] >> impl_tac
     >- (conj_tac
         >- (rpt strip_tac >> irule slice_main_slots >> qexists `tops` >> simp[]) >>
         strip_tac >> drule_all linked_checked_body_type_facts >>
         simp[linked_body_type_facts_def]) >>
     simp[artifact_env_def]) >>
  drule slice_bare_assignable_consistent >> strip_tac >>
  drule_all slice_supported_from_data >> simp[]
QED
