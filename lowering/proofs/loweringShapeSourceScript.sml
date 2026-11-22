(* Source guards for checked runtime and deploy lowering. *)
Theory loweringShapeSource
Ancestors
  list alist option loweringShapeProps vyperTypeSystem vyperTypeContract
  vyperTypeContractContext supportedProgram supportedExprTraverse
  supportedStmtTraverse compileVyper constSubst constSubstCorrect vyperAST supportedNames

Definition expr_raw_shape_root_def:
  expr_raw_shape_root e <=>
    (?ty flags es d. e = Call ty (RawCallCalldataTarget flags) es d) \/
    (?ty salted rof order es d.
       e = Call ty (CreateTarget CreateCopyOf salted rof order) es d) \/
    (?ty blueprint salted rof order es d.
       e = Call ty (CreateTarget (CreateFromBlueprint blueprint) salted rof order) es d)
End

Definition expr_raw_shape_root_mode_def:
  expr_raw_shape_root_mode static e <=> static /\ expr_raw_shape_root e
End

Theorem expr_raw_shape_root_mode_static:
  expr_raw_shape_root_mode T = expr_raw_shape_root
Proof
  simp[FUN_EQ_THM, expr_raw_shape_root_mode_def]
QED

Definition raw_shape_free_program_def:
  raw_shape_free_program tops <=>
    !vis mut nr rr name args dflts ret body.
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
      vis <> Deploy ==>
      ~supported_stmts_expr_exists expr_raw_shape_root body /\
      EVERY (\e. ~supported_expr_exists expr_raw_shape_root e) dflts
End

Definition raw_shape_free_program_mode_def:
  raw_shape_free_program_mode static tops <=>
    !vis mut nr rr name args dflts ret body.
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
      vis <> Deploy ==>
      ~supported_stmts_expr_exists (expr_raw_shape_root_mode static) body /\
      EVERY (\e. ~supported_expr_exists (expr_raw_shape_root_mode static) e) dflts
End

Theorem raw_shape_free_program_mode_static:
  raw_shape_free_program_mode T = raw_shape_free_program
Proof
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD, raw_shape_free_program_mode_def, raw_shape_free_program_def, expr_raw_shape_root_mode_static]
QED

(* Constants cannot introduce the raw-call or msg.gas shape roots. *)
Theorem constant_expr_raw_shape_mode:
  (!e. constant_expr mods e ==> ~supported_expr_exists (expr_raw_shape_root_mode static) e) /\
  (!es. EVERY (constant_expr mods) es ==>
    ~supported_exprs_exists (expr_raw_shape_root_mode static) es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    ~supported_fields_exists (expr_raw_shape_root_mode static) fs)
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, supported_expr_exists_def, expr_raw_shape_root_mode_def, expr_raw_shape_root_def] >>
  rpt strip_tac >> gvs[constant_builtin_def, GSYM EVERY_NOT_EXISTS,
    combinTheory.o_DEF, SF ETA_ss] >>
  gvs[EXISTS_MEM, EVERY_MEM] >> res_tac
QED

Theorem checked_module_consts_env_constant_acc:
  !ts pre E.
    check_contract mode layouts addr mods = SOME artifact /\
    ALOOKUP mods NONE = SOME tops /\ tops = pre ++ ts /\
    (!id r. ALOOKUP E id = SOME r ==> constant_expr mods r) ==>
    !id r. ALOOKUP (module_consts_env ts E) id = SOME r ==> constant_expr mods r
Proof
  Induct >- (simp[module_consts_env_def] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `h` >> simp[module_consts_env_def] >> strip_tac
  >~ [`module_consts_env (VariableDecl vis mut name ty slot :: ts) E`]
  >- (Cases_on `mut` >> gvs[module_consts_env_def]
      >~ [`module_consts_env ts (E ++ [(name,fold_const_expr (subst_consts_expr E e))])`]
      >- (`constant_expr mods e` by
            (irule (cj 1 checked_const_initializer_prefix) >>
             conj_tac >- metis_tac[] >>
             qexistsl [`name`, `pre`, `ts`, `slot`] >> simp[] >> metis_tac[]) >>
          `constant_expr mods (fold_const_expr (subst_consts_expr E e))` by
            metis_tac[subst_consts_constant_expr, fold_const_expr_constant] >>
          rpt strip_tac >> qpat_x_assum `!E'. _ ==> !id r. ALOOKUP (module_consts_env ts E') id = SOME r ==> _` irule >>
          goal_assum (drule_at Any) >>
          rpt strip_tac >> gvs[ALOOKUP_APPEND, AllCaseEqs()] >> metis_tac[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem checked_module_consts_env_replacement_constant:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==> constant_expr mods r
Proof
  strip_tac >> irule checked_module_consts_env_constant_acc >>
  conj_tac >- metis_tac[] >>
  qexistsl [`[]`, `id`, `[]`] >> simp[] >> metis_tac[]
QED

(* ===== Typing gives builtin arity ===== *)

Theorem well_typed_builtin_app_arity:
  well_typed_builtin_app ty bi ts ==> builtin_arity bi <= LENGTH ts
Proof
  Cases_on `bi` >> rw[well_typed_builtin_app_def, builtin_arity_def] >> gvs[]
QED

Theorem well_typed_type_builtin_args_arity:
  well_typed_type_builtin_args tb target ts ==>
  type_builtin_arity tb <= LENGTH ts
Proof
  Cases_on `tb` >>
  rw[well_typed_type_builtin_args_def, type_builtin_arity_def] >> gvs[]
QED

Theorem well_typed_expr_raw_shape_mode[local]:
  (!env e. well_typed_expr env e ==>
     ~supported_expr_exists (expr_raw_shape_root_mode static) e ==>
     ~supported_expr_exists (expr_shape_root_mode static) e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
     ~supported_expr_exists (expr_raw_shape_root_mode static) e ==>
     ~supported_expr_exists (expr_shape_root_mode static) e) /\
  (!env t vt. type_place_target env t = SOME vt ==>
     ~supported_target_exists (expr_raw_shape_root_mode static) t ==>
     ~supported_target_exists (expr_shape_root_mode static) t) /\
  (!env es. well_typed_exprs env es ==>
     ~supported_exprs_exists (expr_raw_shape_root_mode static) es ==>
     ~supported_exprs_exists (expr_shape_root_mode static) es) /\
  (!env opt. well_typed_opt env opt ==>
     ~supported_opt_exists (expr_raw_shape_root_mode static) opt ==>
     ~supported_opt_exists (expr_shape_root_mode static) opt) /\
  (!env kes. well_typed_named_exprs env kes ==>
     ~supported_fields_exists (expr_raw_shape_root_mode static) kes ==>
     ~supported_fields_exists (expr_shape_root_mode static) kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[well_typed_expr_def, supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def,
      expr_raw_shape_root_mode_def, expr_raw_shape_root_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> imp_res_tac well_typed_builtin_app_arity >>
  imp_res_tac well_typed_type_builtin_args_arity >> gvs[]
QED

Theorem fold_const_builtin_shape_mode[local]:
  ~supported_expr_exists (expr_shape_root_mode static) (Builtin ty bi es) ==>
  ~supported_expr_exists (expr_shape_root_mode static) (fold_const_builtin ty bi es)
Proof
  strip_tac >> Cases_on `bi` >>
  gvs[fold_const_builtin_def, supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def] >>
  Cases_on `es` >> gvs[supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def] >>
  Cases_on `t` >> gvs[supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def] >>
  Cases_on `h` >> gvs[supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def] >>
  rename1 `Literal aty l` >> Cases_on `l` >>
  gvs[supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def]
QED

Theorem fold_const_shape_mode[local]:
  (!e. ~supported_expr_exists (expr_shape_root_mode static) e ==>
    ~supported_expr_exists (expr_shape_root_mode static) (fold_const_expr e)) /\
  (!t. ~supported_target_exists (expr_shape_root_mode static) t ==>
    ~supported_target_exists (expr_shape_root_mode static) (fold_const_btarget t)) /\
  (!es. ~supported_exprs_exists (expr_shape_root_mode static) es ==>
    ~supported_exprs_exists (expr_shape_root_mode static) (fold_const_exprs es)) /\
  (!d. ~supported_opt_exists (expr_shape_root_mode static) d ==>
    ~supported_opt_exists (expr_shape_root_mode static) (fold_const_opt d)) /\
  (!fs. ~supported_fields_exists (expr_shape_root_mode static) fs ==>
    ~supported_fields_exists (expr_shape_root_mode static) (fold_const_fields fs))
Proof
  ho_match_mp_tac fold_const_expr_ind >>
  rpt conj_tac >> rpt gen_tac
  >~ [`fold_const_expr (Builtin ty bi es)`]
  >- (simp[fold_const_expr_def] >> strip_tac >> strip_tac >>
      irule fold_const_builtin_shape_mode >>
      gvs[supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def,
          fold_const_collection_metadata]) >>
  simp[fold_const_expr_def, supported_expr_exists_def, expr_shape_root_mode_def, expr_shape_root_def,
       fold_const_collection_metadata] >> metis_tac[]
QED

Theorem checked_module_consts_shape_acc_mode[local]:
  !ts pre E.
    check_contract mode layouts addr mods = SOME artifact /\
    ALOOKUP mods NONE = SOME tops /\ tops = pre ++ ts /\
    (!id r. ALOOKUP E id = SOME r ==>
      ~supported_expr_exists (expr_shape_root_mode static) r) ==>
    !id r. ALOOKUP (module_consts_env ts E) id = SOME r ==>
      ~supported_expr_exists (expr_shape_root_mode static) r
Proof
  Induct >- (simp[module_consts_env_def] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `h` >> pure_rewrite_tac[module_consts_env_def] >>
  strip_tac
  >~ [`module_consts_env (VariableDecl vis mut name ty slot :: ts) E`]
  >- (Cases_on `mut` >> pure_rewrite_tac[module_consts_env_def]
      >~ [`module_consts_env ts (E ++ [(name,fold_const_expr (subst_consts_expr E e))])`]
      >- (`constant_expr mods e /\
           well_typed_expr (artifact_env artifact mods NONE) e` by
            (drule_all checked_const_initializer_prefix >> metis_tac[]) >>
          `~supported_expr_exists (expr_shape_root_mode static) e` by
            metis_tac[constant_expr_raw_shape_mode, well_typed_expr_raw_shape_mode] >>
          `~supported_expr_exists (expr_shape_root_mode static)
              (fold_const_expr (subst_consts_expr E e))` by
            metis_tac[subst_consts_expr_shape_mode, fold_const_shape_mode] >>
          first_x_assum (qspec_then `pre ++ [VariableDecl vis (Constant e) name ty slot]` mp_tac) >>
          pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
          disch_then (qspec_then `E ++ [(name,fold_const_expr (subst_consts_expr E e))]` mp_tac) >>
          (impl_tac >- (simp[] >> rpt strip_tac >>
            gvs[ALOOKUP_APPEND, AllCaseEqs()] >> metis_tac[])) >> simp[]) >>
      qmatch_asmsub_abbrev_tac `tops = pre ++ hd::ts` >>
      first_x_assum (qspec_then `pre ++ [hd]` mp_tac) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      disch_then (qspec_then `E` mp_tac) >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `tops = pre ++ hd::ts` >>
  first_x_assum (qspec_then `pre ++ [hd]` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then (qspec_then `E` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem checked_module_consts_env_replacement_shape_mode:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  ~supported_expr_exists (expr_shape_root_mode static) r
Proof
  strip_tac >> irule checked_module_consts_shape_acc_mode >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> qexists `[]` >> simp[]
QED

Theorem well_typed_atarget_raw_shape_mode[local]:
  (!p t. p = (expr_raw_shape_root_mode static) ==>
     !ty. well_typed_atarget env t ty ==>
     ~supported_assignment_exists p t ==>
     ~supported_assignment_exists (expr_shape_root_mode static) t) /\
  (!p ts. p = (expr_raw_shape_root_mode static) ==>
     !tys. LIST_REL (\t ty. well_typed_atarget env t ty) ts tys ==>
     ~supported_assignments_exists p ts ==>
     ~supported_assignments_exists (expr_shape_root_mode static) ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  rw[supported_assignment_exists_def] >>
  gvs[well_typed_atarget_def, well_typed_target_def, LIST_REL_CONS1] >>
  imp_res_tac well_typed_expr_raw_shape_mode >> res_tac >> gvs[]
QED

Theorem atarget_accepts_raw_shape_mode[local]:
  atarget_accepts env tgt t /\
  ~supported_assignment_exists (expr_raw_shape_root_mode static) tgt ==>
  ~supported_assignment_exists (expr_shape_root_mode static) tgt
Proof
  Cases_on `tgt` >>
  simp[atarget_accepts_def, supported_assignment_exists_def] >>
  rpt strip_tac
  >- (rename1 `type_place_target env b` >>
      Cases_on `type_place_target env b` >> fs[] >>
      metis_tac[well_typed_expr_raw_shape_mode]) >>
  metis_tac[well_typed_atarget_raw_shape_mode, supported_assignment_exists_def]
QED

Theorem well_typed_iterator_raw_shape_mode[local]:
  well_typed_iterator env typ it /\
  ~supported_iterator_exists (expr_raw_shape_root_mode static) it ==>
  ~supported_iterator_exists (expr_shape_root_mode static) it
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def, supported_iterator_exists_def] >>
  metis_tac[well_typed_expr_raw_shape_mode]
QED

Theorem type_stmt_raw_shape_mode:
  (!env ret s env1. type_stmt env ret s = SOME env1 ==>
     ~supported_stmt_expr_exists (expr_raw_shape_root_mode static) s ==>
     ~supported_stmt_expr_exists (expr_shape_root_mode static) s) /\
  (!env ret ss env1. type_stmts env ret ss = SOME env1 ==>
     ~supported_stmts_expr_exists (expr_raw_shape_root_mode static) ss ==>
     ~supported_stmts_expr_exists (expr_shape_root_mode static) ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs(),
      IS_SOME_EXISTS, supported_assert_exists_def, supported_raise_exists_def,
      supported_iterator_exists_def, well_typed_iterator_def,
      well_typed_custom_error_def, well_typed_target_def,
      GSYM supported_exprs_exists_every, supported_expr_exists_def] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> imp_res_tac well_typed_expr_raw_shape_mode >>
  imp_res_tac atarget_accepts_raw_shape_mode >>
  imp_res_tac well_typed_iterator_raw_shape_mode >> gvs[]
QED

(* ===== The checker's facts about the main module ===== *)

Theorem classify_internal_names_fn_sig_keys[local]:
  !src tops.
    MAP (\p. (src, FST (SND (SND (SND p)))))
      (FST (SND (classify_functions tops))) =
    FLAT (MAP (fn_sig_keys_toplevel F src) tops)
Proof
  gen_tac >>
  `!env (fs : (function_mutability # bool # bool # string #
       (string # type) list # expr list # type # stmt list) list).
     MAP (\p. (src, FST (SND (SND (SND p)))))
       (MAP (subst_consts_fn env) fs) =
       MAP (\p. (src, FST (SND (SND (SND p))))) fs` by
    (gen_tac >> Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
     simp[subst_consts_fn_def]) >>
  simp[classify_functions_def] >> Induct >> simp[] >>
  rpt gen_tac >>
  Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `r` >> Cases_on `h` >>
  gvs[classify_function_def, fn_sig_keys_toplevel_def] >>
  BasicProvers.every_case_tac >> gvs[include_fn_sig_def, subst_consts_fn_def] >> rw[]
QED

Theorem ALL_DISTINCT_MAP_name_key[local]:
  !l. ALL_DISTINCT (MAP (\p. (c, FST (SND (SND (SND p))))) l) ==>
      ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p)))) l)
Proof
  Induct >> rw[MEM_MAP] >> metis_tac[]
QED

Theorem check_contract_internal_names_distinct:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                  (FST (SND (classify_functions tops))))
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, contract_keys_def,
       GSYM classify_internal_names_fn_sig_keys] >>
  strip_tac >> drule ALL_DISTINCT_MAP_name_key >> simp[]
QED

Theorem well_typed_exprs_raw_shape_mode[local]:
  !es env. well_typed_exprs env es /\
    EVERY (\e. ~supported_expr_exists (expr_raw_shape_root_mode static) e) es ==>
    EVERY (\e. ~supported_expr_exists (expr_shape_root_mode static) e) es
Proof
  Induct >> simp[well_typed_expr_def] >> metis_tac[well_typed_expr_raw_shape_mode]
QED

Theorem checked_runtime_function_body_shape_mode:
  !layouts addr tops art vis mut nr rr name args dflts ret body.
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  raw_shape_free_program_mode static tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
  vis <> Deploy ==>
  ~supported_stmts_expr_exists (expr_shape_root_mode static) body
Proof
  rw[raw_shape_free_program_mode_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
  drule check_contract_runtime_function_body_MEM >> simp[] >>
  disch_then drule_all >>
  simp[check_function_body_def, IS_SOME_EXISTS] >> strip_tac >>
  metis_tac[type_stmt_raw_shape_mode, well_typed_exprs_raw_shape_mode]
QED

Theorem checked_runtime_function_defaults_shape_mode[local]:
  !layouts addr tops art vis mut nr rr name args dflts ret body.
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  raw_shape_free_program_mode static tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
  vis <> Deploy ==>
  EVERY (\e. ~supported_expr_exists (expr_shape_root_mode static) e) dflts
Proof
  rw[raw_shape_free_program_mode_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
  drule check_contract_runtime_function_body_MEM >> simp[] >>
  disch_then drule_all >>
  simp[check_function_body_def, IS_SOME_EXISTS] >> strip_tac >>
  metis_tac[well_typed_exprs_raw_shape_mode]
QED

Theorem checked_deploy_function_raw_shape_mode:
  !layouts addr tops art vis mut nr rr name args dflts ret source_body.
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret source_body) tops /\
  ~supported_stmts_expr_exists (expr_raw_shape_root_mode static) source_body /\
  ~supported_exprs_exists (expr_raw_shape_root_mode static) dflts ==>
  ~supported_stmts_expr_exists (expr_shape_root_mode static) source_body /\
  ~supported_exprs_exists (expr_shape_root_mode static) dflts
Proof
  rpt gen_tac >> strip_tac >>
  `check_function_body layouts addr [(NONE,tops)] art NONE vis mut nr args
     dflts ret source_body` by
    (drule check_contract_deploy_function_body_MEM >> simp[] >>
     disch_then (drule_at (Pat `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) _`)) >>
     simp[]) >>
  fs[check_function_body_def, IS_SOME_EXISTS] >>
  metis_tac[type_stmt_raw_shape_mode, well_typed_expr_raw_shape_mode]
QED

Theorem check_contract_runtime_bodies_shape_ok_mode:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  raw_shape_free_program_mode static tops ==>
  (runtime_bodies_shape_mode_ok static) tops
Proof
  strip_tac >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
     ~supported_expr_exists (expr_shape_root_mode static) r` by
    (rpt gen_tac >> disch_tac >> irule checked_module_consts_env_replacement_shape_mode >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!vis mut nr rr name args dflts ret body.
    MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\ vis <> Deploy ==>
    ~supported_stmts_expr_exists (expr_shape_root_mode static) body` by
    metis_tac[checked_runtime_function_body_shape_mode] >>
  `!vis mut nr rr name args dflts ret body.
    MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\ vis <> Deploy ==>
    EVERY (\e. ~supported_expr_exists (expr_shape_root_mode static) e) dflts` by
    metis_tac[checked_runtime_function_defaults_shape_mode] >>
  pure_rewrite_tac[runtime_bodies_shape_mode_ok_def] >>
  rpt gen_tac >> strip_tac
  >- suspend "external"
  >- suspend "internal" >>
  suspend "fallback"
QED

Resume check_contract_runtime_bodies_shape_ok_mode[external]:
  drule classify_functions_external_source >> strip_tac >>
      gvs[subst_consts_fn_def]
      >- (conj_tac
          >- (irule (cj 2 subst_consts_stmt_shape_mode) >> simp[] >>
              metis_tac[function_visibility_distinct]) >>
          pure_rewrite_tac[EVERY_NOT_EXISTS] >> BETA_TAC >>
          pure_rewrite_tac[NOT_CLAUSES] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >>
          pure_rewrite_tac[GSYM supported_exprs_exists_every] >>
          irule (cj 3 subst_consts_expr_shape_mode) >> simp[] >>
          gvs[supported_exprs_exists_every, EVERY_MEM, EXISTS_MEM] >>
          metis_tac[function_visibility_distinct]) >>
      conj_tac
      >- (irule (cj 2 subst_consts_stmt_shape_mode) >> simp[] >>
          metis_tac[public_getter_body_shape_mode]) >>
      qpat_x_assum `public_getter _ = SOME _` mp_tac >>
      Cases_on `top` >> simp[public_getter_def] >>
      rpt gen_tac >> Cases_on `v` >> simp[public_getter_def, vyperGetterTheory.getter_def] >>
      rpt CASE_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
      strip_tac >> gvs[subst_consts_expr_def]
QED

Resume check_contract_runtime_bodies_shape_ok_mode[internal]:
  gvs[MEM_classify_internal, subst_consts_fn_def] >>
      conj_tac
      >- (irule (cj 2 subst_consts_stmt_shape_mode) >> simp[] >>
          metis_tac[function_visibility_distinct]) >>
      pure_rewrite_tac[EVERY_NOT_EXISTS] >> BETA_TAC >>
          pure_rewrite_tac[NOT_CLAUSES] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >>
          pure_rewrite_tac[GSYM supported_exprs_exists_every] >>
      irule (cj 3 subst_consts_expr_shape_mode) >> simp[] >>
      gvs[supported_exprs_exists_every, EVERY_MEM, EXISTS_MEM] >>
      metis_tac[function_visibility_distinct]
QED

Resume check_contract_runtime_bodies_shape_ok_mode[fallback]:
  drule classify_functions_fallback_mem >> strip_tac >>
  gvs[subst_consts_fn_def] >>
  conj_tac
  >- (irule (cj 2 subst_consts_stmt_shape_mode) >> simp[] >>
      metis_tac[function_visibility_distinct]) >>
  pure_rewrite_tac[EVERY_NOT_EXISTS] >> BETA_TAC >>
          pure_rewrite_tac[NOT_CLAUSES] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >>
          pure_rewrite_tac[GSYM supported_exprs_exists_every] >>
  irule (cj 3 subst_consts_expr_shape_mode) >> simp[] >>
  gvs[supported_exprs_exists_every, EVERY_MEM, EXISTS_MEM] >>
  metis_tac[function_visibility_distinct]
QED

Finalise check_contract_runtime_bodies_shape_ok_mode

(* S2 from the checker. *)
Theorem lower_vyper_runtime_unit_source_unit_ok_checked_mode:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    raw_shape_free_program_mode static tops ==>
    o1_source_unit_ok unit
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_source_unit_ok_shape_mode >>
  disch_then (qspec_then `static` mp_tac) >> impl_tac
  >- metis_tac[check_contract_runtime_bodies_shape_ok_mode,
               check_contract_internal_names_distinct] >>
  simp[]
QED

(* The checked runtime unit has no DALLOCA. *)
Theorem lower_vyper_runtime_unit_no_dalloca_checked_mode:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    raw_shape_free_program_mode static tops ==>
    (static ==> EVERY (\fn. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts fn))
      unit.cu_context.ctx_functions)
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_no_dalloca_mode >>
  disch_then (qspec_then `static` mp_tac) >> impl_tac
  >- metis_tac[check_contract_runtime_bodies_shape_ok_mode,
               check_contract_internal_names_distinct] >>
  simp[]
QED

(* With DALLOCA permitted, the raw source guard has no excluded roots. *)
Theorem dynamic_raw_expr_shape:
  (!p e. (p = expr_raw_shape_root_mode F) ==> ~supported_expr_exists p e) /\
  (!p t. (p = expr_raw_shape_root_mode F) ==> ~supported_target_exists p t) /\
  (!p es. (p = expr_raw_shape_root_mode F) ==> ~supported_exprs_exists p es) /\
  (!p opt. (p = expr_raw_shape_root_mode F) ==> ~supported_opt_exists p opt) /\
  (!p fs. (p = expr_raw_shape_root_mode F) ==> ~supported_fields_exists p fs)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  rw[supported_expr_exists_def, expr_raw_shape_root_mode_def]
QED

Theorem dynamic_raw_assignment_shape[local]:
  (!p t. (p = expr_raw_shape_root_mode F) ==> ~supported_assignment_exists p t) /\
  (!p ts. (p = expr_raw_shape_root_mode F) ==> ~supported_assignments_exists p ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  rw[supported_assignment_exists_def, dynamic_raw_expr_shape]
QED

Theorem dynamic_raw_stmt_aux_shape[local]:
  (!it. ~supported_iterator_exists (expr_raw_shape_root_mode F) it) /\
  (!r. ~supported_assert_exists (expr_raw_shape_root_mode F) r) /\
  (!r. ~supported_raise_exists (expr_raw_shape_root_mode F) r)
Proof
  rpt conj_tac >> Cases >>
  simp[supported_iterator_exists_def, supported_assert_exists_def,
       supported_raise_exists_def, EXISTS_MEM, dynamic_raw_expr_shape]
QED

Theorem dynamic_raw_stmt_shape:
  (!p s. (p = expr_raw_shape_root_mode F) ==> ~supported_stmt_expr_exists p s) /\
  (!p ss. (p = expr_raw_shape_root_mode F) ==> ~supported_stmts_expr_exists p ss)
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  rw[supported_stmt_expr_exists_def, dynamic_raw_expr_shape,
     dynamic_raw_assignment_shape, dynamic_raw_stmt_aux_shape]
QED

(* ===== supported_program excludes the raw shape roots ===== *)

Theorem supported_assignment_exists_mono[local]:
  (!p t. !q. (!x. p x ==> q x) /\ supported_assignment_exists p t ==>
     supported_assignment_exists q t) /\
  (!p ts. !q. (!x. p x ==> q x) /\ supported_assignments_exists p ts ==>
     supported_assignments_exists q ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  rw[supported_assignment_exists_def] >>
  metis_tac[supported_expr_exists_mono]
QED

Theorem supported_stmt_parts_exists_mono[local]:
  (!x. p x ==> q x) ==>
  (supported_iterator_exists p it ==> supported_iterator_exists q it) /\
  (supported_assert_exists p a ==> supported_assert_exists q a) /\
  (supported_raise_exists p r ==> supported_raise_exists q r)
Proof
  strip_tac >> rpt conj_tac
  >- (Cases_on `it` >> rw[supported_iterator_exists_def] >>
      metis_tac[supported_expr_exists_mono])
  >- (Cases_on `a` >> rw[supported_assert_exists_def, EXISTS_MEM] >>
      metis_tac[supported_expr_exists_mono]) >>
  Cases_on `r` >> rw[supported_raise_exists_def, EXISTS_MEM] >>
  metis_tac[supported_expr_exists_mono]
QED

Theorem supported_stmt_expr_exists_mono:
  (!p s. !q. (!x. p x ==> q x) /\ supported_stmt_expr_exists p s ==>
     supported_stmt_expr_exists q s) /\
  (!p ss. !q. (!x. p x ==> q x) /\ supported_stmts_expr_exists p ss ==>
     supported_stmts_expr_exists q ss)
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  rw[supported_stmt_expr_exists_def] >>
  metis_tac[supported_expr_exists_mono, supported_assignment_exists_mono,
            supported_stmt_parts_exists_mono]
QED

Theorem subst_consts_fn_names:
  !env (fs : (function_mutability # bool # bool # string #
       (string # type) list # expr list # type # stmt list) list).
    MAP (\p. FST (SND (SND (SND p)))) (MAP (subst_consts_fn env) fs) =
    MAP (\p. FST (SND (SND (SND p)))) fs
Proof
  gen_tac >> Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[subst_consts_fn_def]
QED

Theorem classify_fold_internal_name_mem:
  !tops name.
    MEM name (MAP (\p. FST (SND (SND (SND p))))
      (FST (SND (FOLDR classify_function ([],[],NONE,NONE) tops)))) ==>
    MEM name (supported_function_names tops)
Proof
  simp[MEM_MAP, pairTheory.EXISTS_PROD, PULL_EXISTS,
       classify_fold_internal, MEM_supported_function_names] >>
  metis_tac[]
QED

Theorem classify_fold_internal_names_distinct:
  !tops. ALL_DISTINCT (supported_function_names tops) ==>
    ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
      (FST (SND (FOLDR classify_function ([],[],NONE,NONE) tops))))
Proof
  Induct >- simp[] >> rpt strip_tac >>
  qspec_then `tops` assume_tac classify_fold_internal_name_mem >>
  Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `r` >> Cases_on `h` >>
  gvs[classify_function_def, supported_function_names_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >> gvs[] >> rw[] >> metis_tac[]
QED

(* supported_program's distinct function names keep the internal ones
   apart, as lower_vyper_runtime_unit_source_unit_ok_shape asks. *)
Theorem supported_names_internal_names_distinct:
  !tops. ALL_DISTINCT (supported_function_names tops) ==>
         ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                         (FST (SND (classify_functions tops))))
Proof
  gen_tac >>
  Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `r` >>
  simp[classify_functions_def, subst_consts_fn_names] >>
  mp_tac (Q.SPEC `tops` classify_fold_internal_names_distinct) >> simp[]
QED

(* The static shape facts used by the existing clients. *)

Theorem constant_expr_raw_shape:
  (!e. constant_expr mods e ==> ~supported_expr_exists expr_raw_shape_root e) /\
  (!es. EVERY (constant_expr mods) es ==>
    ~supported_exprs_exists expr_raw_shape_root es) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) ==>
    ~supported_fields_exists expr_raw_shape_root fs)
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [expr_raw_shape_root_mode_static]
    (Q.INST [`static` |-> `T`] constant_expr_raw_shape_mode))
QED

Theorem checked_module_consts_env_replacement_shape:
  check_contract mode layouts addr mods = SOME artifact /\
  ALOOKUP mods NONE = SOME tops /\
  ALOOKUP (module_consts_env tops []) id = SOME r ==>
  ~supported_expr_exists expr_shape_root r
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [expr_shape_root_mode_static]
    (Q.INST [`static` |-> `T`] checked_module_consts_env_replacement_shape_mode))
QED

Theorem type_stmt_raw_shape:
  (!env ret s env1. type_stmt env ret s = SOME env1 ==>
     ~supported_stmt_expr_exists expr_raw_shape_root s ==>
     ~supported_stmt_expr_exists expr_shape_root s) /\
  (!env ret ss env1. type_stmts env ret ss = SOME env1 ==>
     ~supported_stmts_expr_exists expr_raw_shape_root ss ==>
     ~supported_stmts_expr_exists expr_shape_root ss)
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [expr_shape_root_mode_static, expr_raw_shape_root_mode_static]
    (Q.INST [`static` |-> `T`] type_stmt_raw_shape_mode))
QED

Theorem checked_runtime_function_body_shape:
  !layouts addr tops art vis mut nr rr name args dflts ret body.
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  raw_shape_free_program tops /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
  vis <> Deploy ==>
  ~supported_stmts_expr_exists expr_shape_root body
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [expr_shape_root_mode_static, raw_shape_free_program_mode_static]
    (Q.INST [`static` |-> `T`] checked_runtime_function_body_shape_mode))
QED

Theorem checked_deploy_function_raw_shape:
  !layouts addr tops art vis mut nr rr name args dflts ret source_body.
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret source_body) tops /\
  ~supported_stmts_expr_exists expr_raw_shape_root source_body /\
  ~supported_exprs_exists expr_raw_shape_root dflts ==>
  ~supported_stmts_expr_exists expr_shape_root source_body /\
  ~supported_exprs_exists expr_shape_root dflts
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [expr_shape_root_mode_static, expr_raw_shape_root_mode_static]
    (Q.INST [`static` |-> `T`] checked_deploy_function_raw_shape_mode))
QED

Theorem check_contract_runtime_bodies_shape_ok:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  raw_shape_free_program tops ==>
  runtime_bodies_shape_ok tops
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [raw_shape_free_program_mode_static, runtime_bodies_shape_mode_ok_static]
    (Q.INST [`static` |-> `T`] check_contract_runtime_bodies_shape_ok_mode))
QED

Theorem lower_vyper_runtime_unit_source_unit_ok_checked:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    raw_shape_free_program tops ==>
    o1_source_unit_ok unit
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [raw_shape_free_program_mode_static]
    (Q.INST [`static` |-> `T`] lower_vyper_runtime_unit_source_unit_ok_checked_mode))
QED

Theorem lower_vyper_runtime_unit_no_dalloca_checked:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    raw_shape_free_program tops ==>
    EVERY (\fn. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts fn))
      unit.cu_context.ctx_functions
Proof
  mp_tac (Q.INST [`static` |-> `T`] lower_vyper_runtime_unit_no_dalloca_checked_mode) >>
  simp_tac bool_ss [raw_shape_free_program_mode_static]
QED
