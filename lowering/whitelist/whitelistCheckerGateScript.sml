(* Whitelist removal: every single-module program check_contract accepts is
   in the supported_* gate.

   TOP-LEVEL: check_contract_supported_program (runtime check and the
   layouts the call relation fixes) and check_contract_supported_program_deploy
   (deployment check). The four top theorems discharge their gate through
   these, so neither is assumed whole: each conjunct of the gate has its own
   lemma below.

   - Storage, transient and hashmap slots: the checker reads them from the
     layouts and ignores the AST annotation, so headers and bodies (whose
     storage clauses ask for the annotation) take layouts_agree, which the
     call and deployment relations carry; the checker allocates every
     variable (check_contract_main_module_allocated). Types come from
     assignable_type.
   - Function bodies and defaults: from check_function_body. The statement
     and expression layers carry the typing environment of the body, which
     extends the artifact's and binds exactly the arguments, locals and loop
     variables; custom-error reasons come from custom_errors_stmt_ok.
   - Constants: from the checker's constant typing. *)
Theory whitelistCheckerGate
Ancestors
  list rich_list pair alist finite_map pred_set vyperAST vyperTypeSystem vyperTypeContract
  vyperTypeContractContext vyperContext
  e2eDefs e2eDeployDefs
  supportedTypes supportedDecls supportedNames supportedExprs supportedExprForms
  supportedStmts
  supportedStmtTraverse supportedProgram
  whitelistCheckerDecls whitelistCheckerDeploy whitelistCheckerTypes
  whitelistCheckerProgram

(* ===== Runtime gate ===== *)

Triviality assignable_type_supported_nested:
  !tenv ty. assignable_type tenv ty ==>
    !fuel tops leaf.
      CARD (FDOM tenv) <= fuel /\
      (!id args. FLOOKUP tenv id = SOME (StructArgs args) ==>
                 supported_struct_fields tops id = SOME args) /\
      (!t. supported_scalar_type t ==> leaf t) ==>
      supported_nested_type leaf fuel tops ty
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`BaseT bt`]
  >- (rw[assignable_type_def, Once supported_nested_type_def] >>
      first_x_assum irule >>
      drule well_formed_base_scalar >>
      rw[supported_scalar_type_def, supported_word_type_def] >>
      gvs[supported_word_type_def])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >> fs[assignable_type_def, EVERY_MEM] >>
      ONCE_REWRITE_TAC[supported_nested_type_def] >>
      disj2_tac >> simp[EVERY_MEM, NULL_EQ] >> metis_tac[])
  >~ [`ArrayT elem bd`]
  >- (rpt strip_tac >>
      fs[assignable_type_def] >>
      ONCE_REWRITE_TAC[supported_nested_type_def] >>
      Cases_on `bd` >> simp[] >>
      metis_tac[well_formed_fixed_array_nonempty])
  >~ [`StructT id`]
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP tenv id` >> fs[assignable_type_def] >>
      rename1 `FLOOKUP tenv id = SOME desc` >>
      Cases_on `desc` >> fs[] >>
      rename1 `FLOOKUP tenv id = SOME (StructArgs args)` >>
      `id IN FDOM tenv` by gvs[flookup_thm] >>
      `0 < CARD (FDOM tenv)` by
        (spose_not_then assume_tac >>
         `CARD (FDOM tenv) = 0` by decide_tac >>
         gvs[CARD_EQ_0, FDOM_FINITE]) >>
      `CARD (FDOM (tenv \\ id)) = CARD (FDOM tenv) - 1` by
        simp[FDOM_DOMSUB, CARD_DELETE, FDOM_FINITE] >>
      `fuel <> 0` by decide_tac >>
      `supported_struct_fields tops id = SOME args` by metis_tac[] >>
      ONCE_REWRITE_TAC[supported_nested_type_def] >>
      simp[EVERY_MEM, NULL_EQ] >> disj2_tac >> rpt strip_tac >>
      first_x_assum irule >>
      gvs[EVERY_MEM, DOMSUB_FLOOKUP_THM, AllCaseEqs()] >>
      metis_tac[DECIDE ``a <= b ==> a - 1 <= b - 1:num``])
  >~ [`FlagT id`]
  >- (rw[Once supported_nested_type_def] >>
      first_x_assum irule >> simp[supported_scalar_type_def])
  >> simp[assignable_type_def]
QED

Triviality assignable_type_supported_place:
  assignable_type (type_env tops) ty ==> supported_place_type tops ty
Proof
  rw[supported_place_type_def] >>
  drule assignable_type_supported_nested >>
  disch_then irule >>
  simp[type_env_struct_fields, type_env_def, type_env_card_le]
QED

Triviality assignable_type_supported_event:
  assignable_type (type_env tops) ty ==>
  supported_nested_type supported_event_leaf_type (LENGTH tops) tops ty
Proof
  strip_tac >> drule assignable_type_supported_nested >>
  disch_then irule >>
  simp[type_env_struct_fields, type_env_def, type_env_card_le,
       supported_event_leaf_type_def]
QED

Triviality checker_hashmap_key_supported:
  well_formed_type tenv ty /\ hashmap_key_type ty ==>
  supported_hashmap_key_type ty
Proof
  Cases_on `ty` >> simp[hashmap_key_type_def, supported_hashmap_key_type_def]
  >- (rename1 `BaseT bt` >> strip_tac >>
      drule well_formed_base_scalar >> strip_tac >>
      Cases_on `bt` >> gvs[hashmap_key_type_def, supported_scalar_type_def,
                             supported_word_type_def]) >>
  simp[supported_scalar_type_def]
QED

Triviality checker_hashmap_value_supported:
  !vt. check_value_type (type_env tops) vt ==> supported_hashmap_value tops vt
Proof
  Induct >> simp[check_value_type_def, supported_hashmap_value_def,
                  supported_storage_type_def, GSYM supported_place_type_def] >>
  metis_tac[assignable_type_supported_place, checker_hashmap_key_supported]
QED

Triviality checker_indexed_event_type_supported:
  assignable_type tenv ty /\ event_indexable_type ty ==>
  supported_event_leaf_type ty
Proof
  Cases_on `ty` >> simp[event_indexable_type_def, supported_event_leaf_type_def]
  >- (strip_tac >> fs[assignable_type_def] >>
      drule well_formed_base_scalar >> strip_tac >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[supported_scalar_type_def, supported_word_type_def]) >>
  simp[supported_scalar_type_def]
QED

Triviality layouts_agree_allocated_header:
  layouts_agree tops am tx /\ MEM tl tops /\
  toplevel_allocated am.layouts tx.target NONE tl ==>
  case tl of
    VariableDecl _ Storage _ _ slot => IS_SOME slot
  | VariableDecl _ Transient _ _ slot => IS_SOME slot
  | HashMapDecl _ _ _ _ _ slot => IS_SOME slot
  | _ => T
Proof
  Cases_on `tl` >> simp[] >>
  TRY (rename1 `VariableDecl _ mut` >> Cases_on `mut`) >>
  simp[toplevel_allocated_def, layouts_agree_def, lookup_var_slot_in_layouts_def] >>
  Cases_on `ALOOKUP am.layouts tx.target` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  metis_tac[]
QED

Triviality checker_supported_declaration_header:
  check_toplevel_decl [(NONE, tops)] art NONE tl /\
  (case tl of
     VariableDecl _ Storage _ _ slot => IS_SOME slot
   | VariableDecl _ Transient _ _ slot => IS_SOME slot
   | HashMapDecl _ _ _ _ _ slot => IS_SOME slot
   | _ => T) ==>
  supported_declaration_header tops tl
Proof
  Cases_on `tl` >>
  simp[check_toplevel_decl_def, supported_declaration_header_def,
       type_env_all_modules_def, FUNION_FEMPTY_2, GSYM type_env_def]
  >- (rename1 `supported_function_return tops vis ret` >>
      Cases_on `vis` >>
      simp[function_header_ok_def, supported_function_return_def,
           supported_return_type_def] >>
      metis_tac[assignable_type_supported_place])
  >- (Cases_on `v0` >> Cases_on `o'` >>
      simp[check_toplevel_decl_def, supported_declaration_header_def,
           type_env_all_modules_def, FUNION_FEMPTY_2, GSYM type_env_def, supported_storage_type_def,
           GSYM supported_place_type_def, supported_value_type_def,
           assignable_type_supported_place])
  >- (rename1 `IS_SOME slot` >> Cases_on `slot` >>
      simp[check_toplevel_decl_def, supported_declaration_header_def,
           type_env_all_modules_def, FUNION_FEMPTY_2, GSYM type_env_def] >>
      metis_tac[checker_hashmap_key_supported, checker_hashmap_value_supported])
  >- (simp[EVERY_MEM, FORALL_PROD, NULL_EQ] >>
      metis_tac[assignable_type_supported_place])
  >> simp[FILTER_MAP, combinTheory.I_o_ID, EVERY_MEM, FORALL_PROD]
  >> rw[]
  >> metis_tac[assignable_type_supported_event, checker_indexed_event_type_supported]
QED

Theorem check_contract_supported_declaration_headers:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_declaration_headers tops
Proof
  rw[supported_declaration_headers_def, EVERY_MEM] >>
  rename1 `MEM tl tops` >>
  drule_all check_contract_single_decl >> strip_tac >>
  drule check_contract_main_module_allocated >>
  simp[module_allocated_def, EVERY_MEM] >>
  disch_then (drule_then assume_tac) >>
  metis_tac[layouts_agree_allocated_header, checker_supported_declaration_header]
QED

Theorem check_contract_supported_internal_function_names:
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

Theorem check_contract_supported_function_body:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  supported_function_body tops vis args fbody
Proof
  cheat
QED

Theorem check_contract_supported_defaults:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret fbody) tops /\
  vis <> Deploy ==>
  EVERY (supported_default_expression tops) dflts /\
  supported_pure_exprs tops dflts
Proof
  cheat
QED

Theorem check_contract_supported_consts:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  EVERY (supported_pure_expr tops o SND) (module_consts_env tops [])
Proof
  cheat
QED

Theorem check_contract_supported_declaration_bodies:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  EVERY (supported_declaration_body tops) tops
Proof
  rw[EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_declaration_body_def] >>
  metis_tac[check_contract_supported_function_body,
            check_contract_supported_defaults]
QED

(* TOP-LEVEL *)
Theorem check_contract_supported_program:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_program tops
Proof
  metis_tac[supported_program_def, check_contract_supported_declaration_headers,
            check_contract_supported_declaration_names,
            check_contract_supported_internal_function_names,
            check_contract_supported_declaration_bodies,
            check_contract_supported_consts]
QED

(* ===== Deployment gate ===== *)

Theorem check_contract_deploy_function_body:
  check_contract T am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl Deploy mut nr rr name args dflts ret fbody) tops ==>
  EVERY (supported_value_type tops o SND) args /\
  supported_function_body tops Deploy args fbody
Proof
  cheat
QED

(* TOP-LEVEL *)
Theorem check_contract_supported_program_deploy:
  check_contract T am.layouts tx.target [(NONE, tops)] = SOME art /\
  layouts_agree tops am tx ==>
  supported_program_deploy tops
Proof
  rw[supported_program_deploy_def, EVERY_MEM] >> rename1 `MEM tl tops` >>
  Cases_on `tl` >> simp[supported_deploy_declaration_def] >>
  rename1 `FunctionDecl vis` >> Cases_on `vis` >> simp[] >>
  metis_tac[check_contract_deploy_function_body]
QED

(* ===== The gate from the top theorems' typing premises ===== *)

(* TOP-LEVEL *)
Theorem source_typing_ok_supported_program:
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx ==>
  supported_program tops
Proof
  rw[source_typing_ok_def, source_deployment_rel_def] >>
  metis_tac[check_contract_supported_program]
QED

(* TOP-LEVEL *)
Theorem deploy_typing_ok_supported_programs:
  deploy_typing_ok tops am tx /\ layouts_agree tops am tx ==>
  supported_program tops /\ supported_program_deploy tops
Proof
  rw[deploy_typing_ok_def] >>
  metis_tac[check_contract_supported_program,
            check_contract_supported_program_deploy]
QED
