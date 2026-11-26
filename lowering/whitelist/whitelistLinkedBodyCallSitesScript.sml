Theory whitelistLinkedBodyCallSites
Ancestors
  whitelistCheckerDecls constSubstStmtsPreserve constSubstCorrect constSubstMods
  whitelistCheckerCallGraphProps
  vyperTypeCallGraphSoundness vyperTypeContractStaticMaps vyperTypeContract
  vyperTypeCallGraph vyperTypeEvalProofs vyperInterpreter vyperAST alist finite_map list pair

(* Each linked replacement remains a constant expression.  In particular,
   its module-qualified names cannot hide an internal call. *)
Theorem subst_const_mods_constant[local]:
  (!e env. EVERY (constant_expr mods o SND) env /\ constant_expr mods e ==>
     constant_expr mods (subst_consts_expr_mods env e)) /\
  (!es env. EVERY (constant_expr mods o SND) env /\ EVERY (constant_expr mods) es ==>
     EVERY (constant_expr mods) (subst_consts_exprs_mods env es)) /\
  (!fs env. EVERY (constant_expr mods o SND) env /\ EVERY (constant_expr mods) (MAP SND fs) ==>
     EVERY (constant_expr mods) (MAP SND (subst_consts_fields_mods env fs)))
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, subst_consts_expr_mods_def] >>
  rpt strip_tac >> gvs[]
  >~ [`subst_consts_expr_mods _ (TopLevelName _ _)`]
  >- (PairCases_on `ns` >> gvs[subst_consts_expr_mods_def, constant_expr_def] >>
      Cases_on `ALOOKUP env (ns0,ns1)` >> gvs[constant_expr_def] >>
      fs[EVERY_MEM] >> metis_tac[ALOOKUP_MEM, SND]) >>
  metis_tac[]
QED

Theorem module_const_mods_constant[local]:
  !src tops acc.
    (!vis e id ty slot. MEM (VariableDecl vis (Constant e) id ty slot) tops ==>
       constant_expr mods e) /\ EVERY (constant_expr mods o SND) acc ==>
    EVERY (constant_expr mods o SND) (module_consts_env_mods src tops acc)
Proof
  ho_match_mp_tac module_consts_env_mods_ind >>
  simp[module_consts_env_mods_def, EVERY_APPEND] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  reverse conj_tac
  >- (irule (cj 1 fold_const_expr_constant) >>
      irule (cj 1 subst_const_mods_constant) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem const_mods_acc_constant[local]:
  !ordered acc.
    (!src tops vis e id ty slot. MEM (src,tops) ordered /\
       MEM (VariableDecl vis (Constant e) id ty slot) tops ==>
       constant_expr mods e) /\ EVERY (constant_expr mods o SND) acc ==>
    EVERY (constant_expr mods o SND) (consts_env_mods_acc ordered acc)
Proof
  Induct >> simp[consts_env_mods_acc_def] >>
  Cases_on `h` >> rw[consts_env_mods_acc_def] >> first_x_assum irule >>
  conj_tac >- metis_tac[] >>
  irule module_const_mods_constant >> metis_tac[]
QED

Theorem checked_const_mods_constant[local]:
  check_contract mode layouts addr mods = SOME art ==>
  EVERY (constant_expr mods o SND) (consts_env_mods mods)
Proof
  strip_tac >> simp[consts_env_mods_def, consts_env_modules_order_eq] >>
  irule const_mods_acc_constant >>
  simp[MEM_constants_order] >> rpt strip_tac >>
  `ALOOKUP mods src = SOME tops` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[] >>
     drule check_contract_artifact_fields >> simp[contract_namespaces_ok_def]) >>
  drule_all check_contract_toplevel_decl_MEM_checked >> simp[check_toplevel_decl_def]
QED

Theorem subst_const_mods_int_calls[local]:
  (!env e. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_expr (subst_consts_expr_mods env e) = int_calls_expr e) /\
  (!env t. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_target (subst_consts_btarget_mods env t) = int_calls_target t) /\
  (!env es. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_exprs (subst_consts_exprs_mods env es) = int_calls_exprs es) /\
  (!env opt. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_opt (subst_consts_opt_mods env opt) = int_calls_opt opt) /\
  (!env fs. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_named_exprs (subst_consts_fields_mods env fs) = int_calls_named_exprs fs)
Proof
  ho_match_mp_tac subst_consts_expr_mods_ind >>
  rpt strip_tac >> res_tac >> gvs[subst_consts_expr_mods_def, int_calls_expr_def]
  >~ [`Call`] >- (Cases_on `ct` >> gvs[int_calls_expr_def]) >>
  rpt CASE_TAC >> gvs[int_calls_expr_def] >> res_tac
QED

Theorem subst_const_mods_target_int_calls[local]:
  (!env t. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_atarget (subst_consts_target_mods env t) = int_calls_atarget t) /\
  (!env ts. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_atargets (subst_consts_targets_mods env ts) = int_calls_atargets ts)
Proof
  ho_match_mp_tac subst_consts_target_mods_ind >>
  rpt strip_tac >> res_tac >> gvs[subst_consts_target_mods_def, int_calls_atarget_def] >>
  irule (cj 2 subst_const_mods_int_calls) >> first_assum ACCEPT_TAC
QED

Theorem int_calls_error_list[local]:
  (!es fs. int_calls_exprs (es ++ MAP SND fs) =
           int_calls_exprs es ++ int_calls_named_exprs fs)
Proof
  Induct >> simp[int_calls_expr_def, int_calls_exprs_MAP_SND]
QED

Theorem subst_const_mods_error_int_calls[local]:
  (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
  int_calls_exprs (custom_error_exprs (subst_consts_error_mods env err)) =
  int_calls_exprs (custom_error_exprs err)
Proof
  Cases_on `err` >>
  simp[subst_consts_error_mods_def, custom_error_exprs_def, int_calls_error_list] >>
  metis_tac[cj 3 subst_const_mods_int_calls, cj 5 subst_const_mods_int_calls]
QED

Theorem subst_const_mods_stmt_int_calls[local]:
  (!env s. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_stmt (subst_consts_stmt_mods env s) = int_calls_stmt s) /\
  (!env ss. (!k r. ALOOKUP env k = SOME r ==> int_calls_expr r = []) ==>
     int_calls_stmts (subst_consts_stmts_mods env ss) = int_calls_stmts ss)
Proof
  ho_match_mp_tac subst_consts_stmt_mods_ind >>
  rpt strip_tac >> res_tac >>
  gvs[subst_consts_stmt_mods_def, int_calls_stmt_def]
  >~ [`subst_consts_iter_mods`]
  >- (Cases_on `it` >> simp[subst_consts_iter_mods_def, int_calls_iterator_def] >>
      metis_tac[cj 1 subst_const_mods_int_calls])
  >~ [`subst_consts_areason_mods`]
  >- (Cases_on `r` >> simp[subst_consts_areason_mods_def, int_calls_assert_reason_def] >>
      metis_tac[cj 1 subst_const_mods_int_calls, subst_const_mods_error_int_calls])
  >~ [`subst_consts_rreason_mods`]
  >- (Cases_on `r` >> simp[subst_consts_rreason_mods_def, int_calls_raise_reason_def] >>
      metis_tac[cj 1 subst_const_mods_int_calls, subst_const_mods_error_int_calls]) >>
  metis_tac[subst_const_mods_int_calls, cj 1 subst_const_mods_target_int_calls]
QED

Theorem checked_subst_mods_int_calls[local]:
  check_contract mode layouts addr mods = SOME art ==>
  int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss) =
  int_calls_stmts ss
Proof
  strip_tac >> irule (cj 2 subst_const_mods_stmt_int_calls) >>
  drule checked_const_mods_constant >> simp[EVERY_MEM, FORALL_PROD] >>
  metis_tac[ALOOKUP_MEM, cj 1 constant_expr_no_internal_calls]
QED

Theorem checked_main_deploy_name[local]:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret ss) tops ==>
  name = "__init__"
Proof
  strip_tac >> drule_all check_contract_toplevel_decl_MEM_checked >>
  simp[check_toplevel_decl_def, function_header_ok_def]
QED

(* The only non-internal signature can be a constructor's.  For a main
   constructor, using that main signature would require a self-edge. *)
Theorem linked_checked_main_call_internal:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret ss) tops /\
  FLOOKUP art.cta_fn_sigs (NONE,callee) = SOME sg /\
  (mode ==> vis = Deploy /\
     (MEM (NONE,callee) (function_int_calls dflts ss) \/
      MEM (NONE,callee)
        (int_calls_stmts (subst_consts_stmts_mods (consts_env_mods mods) ss)))) ==>
  IS_SOME (supported_function_decl tops (NONE,callee) Internal)
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  gvs[FLOOKUP_DRESTRICT_SOME] >>
  drule_all build_contract_type_artifact_fn_sigs_declared_sound >> strip_tac >>
  gvs[] >> rename1 `include_fn_sig mode vi` >> Cases_on `vi` >> gvs[include_fn_sig_def]
  >~ [`MEM (FunctionDecl Internal _ _ _ _ _ _ _ _) tops`]
  >- metis_tac[supported_function_decl_internal_MEM] >>
  `name = callee` by metis_tac[checked_main_deploy_name] >> gvs[] >>
  `MEM (NONE,callee) (function_int_calls dflts ss)` by
    (drule checked_subst_mods_int_calls >>
     disch_then (qspec_then `ss` assume_tac) >>
     gvs[function_int_calls_def, MEM_APPEND]) >>
  `MEM ((NONE,callee),(NONE,callee)) (contract_call_edges mods)` by
    (irule contract_call_edges_function >> simp[] >>
     metis_tac[ALOOKUP_MEM]) >>
  drule checked_no_self_call >>
  disch_then (qspec_then `(NONE,callee)` mp_tac) >> simp[]
QED
