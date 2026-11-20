(* SCRATCH SEQ-8389 (never lands): how far check_contract implies the widened
   gate.  Every residual ends in print_tac >> cheat to record its goal; none of
   these is an admission and nothing uses them. *)
Theory gateCheckerAttempt
Ancestors
  list rich_list option vyperAST vyperTypeSystem vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeContractContext
  supportedTypes supportedDecls supportedNames supportedExprs supportedStmts
  supportedProgram supportedStmtTraverse
  whitelistCheckerDecls whitelistCheckerTypes

(* Copies of whitelistCheckerProgram/Deploy lemmas, so this theory stays out
   of the lowering cone that the census is still breaking. *)
Theorem function_names_self_member_sublist[local]:
  !tops.
    sublist (MAP (\n. (NONE, n)) (supported_function_names tops))
            (FLAT (MAP (self_member_keys_toplevel (NONE:num option)) tops))
Proof
  Induct >> simp[supported_function_names_def, sublist_nil] >>
  Cases >>
  simp[supported_function_names_def, self_member_keys_toplevel_def] >>
  simp[GSYM sublist_cons, sublist_cons_include]
QED

Theorem attempt_function_names_distinct[local]:
  check_contract b layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_function_names tops)
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, contract_keys_def] >> strip_tac >>
  irule (INST_TYPE [beta |-> ``:num option # string``] ALL_DISTINCT_MAP) >>
  qexists_tac `\x. (NONE, x)` >>
  irule sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP (self_member_keys_toplevel NONE) tops)` >>
  simp[function_names_self_member_sublist]
QED


Theorem attempt_names[local]:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  supported_declaration_names tops
Proof
  strip_tac >>
  simp[supported_declaration_names_def, EVERY_MEM] >>
  rpt conj_tac
  >- metis_tac[attempt_function_names_distinct]
  >- metis_tac[check_contract_event_names_distinct]
  >- (Cases >> simp[supported_function_header_names_def] >> strip_tac >>
      drule_all check_contract_function_header_bindings >> simp[])
  >- metis_tac[check_contract_selectors_distinct]
QED

Theorem attempt_runtime_checked[local]:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  check_function_body layouts addr [(NONE, tops)] art NONE vis mut nr args
    dflts ret fbody
Proof
  strip_tac >> drule check_contract_main_module_allocated >> simp[] >>
  strip_tac >> drule check_contract_runtime_function_body_MEM >> simp[] >>
  disch_then drule_all >> simp[]
QED

(* The statement layer: what supported_stmt asks of a typed statement, with
   env unconnected to tops (the expression lemmas need that connection). *)
Theorem attempt_stmts:
  (!env ret s env'. type_stmt env ret s = SOME env' ==>
     supported_stmt tops bindings s) /\
  (!env ret ss env'. type_stmts env ret ss = SOME env' ==>
     supported_stmts tops bindings ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once type_stmt_def, supported_stmt_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  cheat (* residuals recorded in checker-stmt-residuals.log *)
QED

Theorem attempt_runtime_bindings[local]:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  ALL_DISTINCT (MAP FST args) /\
  EVERY (\n. ~MEM n (MAP FST args))
    (MAP FST (supported_stmts_bindings T fbody) ++
     MAP FST (supported_stmts_bindings F fbody))
Proof
  strip_tac >> conj_tac
  >- (drule_all check_contract_function_header_bindings >>
      simp[supported_function_bindings_def]) >>
  drule_all check_contract_body_bindings_not_args >> simp[]
QED

Theorem attempt_deploy_checked[local]:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops ==>
  check_toplevel_decl [(NONE, tops)] art NONE
    (FunctionDecl vis mut nr rr name args dflts ret fbody) /\
  check_function_body layouts addr [(NONE, tops)] art NONE vis mut nr args
    dflts ret fbody
Proof
  strip_tac >> conj_tac
  >- (irule check_contract_toplevel_decl_MEM_checked >> simp[] >> metis_tac[])
  >- (irule check_contract_deploy_function_body_MEM >> simp[] >> metis_tac[])
QED

Theorem attempt_deploy_bindings[local]:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops ==>
  ALL_DISTINCT (MAP FST args) /\
  EVERY (\n. ~MEM n (MAP FST args))
    (MAP FST (supported_stmts_bindings T fbody) ++
     MAP FST (supported_stmts_bindings F fbody))
Proof
  strip_tac >> drule_all attempt_deploy_checked >> strip_tac >> conj_tac
  >- gvs[check_toplevel_decl_def, params_ok_def] >>
  gvs[check_function_body_def, IS_SOME_EXISTS] >>
  drule (CONJUNCT2 type_stmt_bindings_fresh) >>
  simp[function_entry_env_var_types_fdom]
QED

(* The type residual every header case reduces to. *)
Theorem attempt_assignable_place:
  !ty. assignable_type (type_env_all_modules [(NONE, tops)]) ty ==>
       supported_place_type tops ty
Proof
  Cases >> simp[assignable_type_def, supported_place_type_def] >>
  ONCE_REWRITE_TAC[supported_nested_type_def] >>
  simp[supported_scalar_type_def] >> rpt strip_tac
  >~ [`BaseT bt`]
  >- (drule well_formed_base_scalar >> strip_tac >>
      gvs[supported_scalar_type_def, supported_word_type_def,
          supported_string_type_def] >>
      goalStack.print_tac "ASSIGNABLE-BASE" >> cheat) >>
  goalStack.print_tac "ASSIGNABLE" >> cheat
QED

Theorem attempt_headers:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  supported_declaration_headers tops
Proof
  rw[supported_declaration_headers_def, EVERY_MEM] >>
  rename1 `MEM tl tops` >>
  drule_all check_contract_single_decl >>
  Cases_on `tl` >>
  simp[supported_declaration_header_def, check_toplevel_decl_def,
       function_header_ok_def] >>
  TRY (rename1 `VariableDecl _ mut _ _ slot` >> Cases_on `mut` >>
       Cases_on `slot`) >>
  TRY (rename1 `HashMapDecl _ _ _ _ _ slot` >> Cases_on `slot`) >>
  TRY (rename1 `FunctionDecl fv` >> Cases_on `fv`) >>
  rpt strip_tac >>
  gvs[NULL_EQ, EVERY_MEM, pairTheory.FORALL_PROD, attempt_assignable_place,
      supported_function_return_def, supported_return_type_def,
      supported_value_type_def, supported_storage_type_def,
      GSYM supported_place_type_def, FILTER_MAP, combinTheory.o_DEF, ETA_AX] >>
  goalStack.print_tac "HDR-REST" >> cheat
QED

Theorem attempt_internal_names:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (supported_internal_function_names tops)
Proof
  strip_tac >>
  drule check_contract_function_names_same_vis_distinct >>
  disch_then (qspec_then `Internal` mp_tac) >> simp[] >>
  `!ts. supported_internal_function_names ts =
        supported_function_names
          (FILTER (\t. ?m nr rr n a d r b.
                     t = FunctionDecl Internal m nr rr n a d r b) ts)`
    suffices_by simp[] >>
  Induct >> simp[supported_internal_function_names_def,
                 supported_function_names_def] >>
  Cases >> simp[supported_function_names_def] >> rw[] >>
  gvs[supported_function_names_def] >>
  rename1 `vis <> Internal` >> Cases_on `vis` >> gvs[]
QED

Theorem attempt_body:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  supported_function_body tops vis args fbody
Proof
  strip_tac >>
  drule_all attempt_runtime_bindings >> strip_tac >>
  drule_all attempt_runtime_checked >>
  simp[supported_function_body_def, check_function_body_def, IS_SOME_EXISTS] >>
  rpt strip_tac >~ [`supported_stmts`] >- metis_tac[attempt_stmts] >>
  goalStack.print_tac "BODY" >> cheat
QED

Theorem attempt_defaults:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  EVERY (supported_default_expression tops) dflts /\
  supported_pure_exprs tops dflts
Proof
  strip_tac >>
  drule_all attempt_runtime_checked >> simp[check_function_body_def] >>
  rpt strip_tac >>
  goalStack.print_tac "DEFAULTS" >> cheat
QED

Theorem attempt_consts:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  EVERY (supported_pure_expr tops o SND) (module_consts_env tops [])
Proof
  strip_tac >>
  qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
  simp[check_contract_def, contract_constants_ok_def] >> rpt strip_tac >>
  goalStack.print_tac "CONSTS" >> cheat
QED

Theorem attempt_bodies:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  EVERY (supported_declaration_body tops) tops
Proof
  rw[EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_declaration_body_def] >>
  metis_tac[attempt_body, attempt_defaults]
QED

Theorem attempt_supported_program:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  supported_program tops
Proof
  metis_tac[supported_program_def, attempt_headers, attempt_names,
            attempt_internal_names, attempt_bodies, attempt_consts]
QED

Theorem attempt_deploy_body:
  check_contract T layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret fbody) tops ==>
  EVERY (supported_value_type tops o SND) args /\
  supported_function_body tops Deploy args fbody
Proof
  strip_tac >>
  drule_all attempt_deploy_bindings >> strip_tac >>
  drule_all attempt_deploy_checked >>
  simp[supported_function_body_def, check_function_body_def, IS_SOME_EXISTS,
       check_toplevel_decl_def, params_ok_def, EVERY_MEM,
       pairTheory.FORALL_PROD, supported_value_type_def] >>
  rpt strip_tac >~ [`supported_stmts`] >- metis_tac[attempt_stmts] >>
  TRY (first_x_assum drule >> metis_tac[attempt_assignable_place]) >>
  goalStack.print_tac "DEPLOY" >> cheat
QED

Theorem attempt_supported_program_deploy:
  check_contract T layouts addr [(NONE, tops)] = SOME art ==>
  supported_program_deploy tops
Proof
  rw[supported_program_deploy_def, EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_deploy_declaration_def] >>
  rename1 `FunctionDecl vis` >> Cases_on `vis` >> simp[] >>
  metis_tac[attempt_deploy_body]
QED
