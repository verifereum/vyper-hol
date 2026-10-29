Theory sourceResolveProps
Ancestors
  sourceResolveModules sourceResolve sourceSyntax sourceConstEnv
  sourceConstAST option alist list pair

Theorem source_resolve_lexical_shadow:
  ALOOKUP scope name = SOME path ==>
  source_resolve_lexical (scope::scopes) name = SOME path
Proof
  simp[source_resolve_lexical_def]
QED

Theorem source_resolve_local_scope_lookup:
  MEM name names ==>
  ALOOKUP (source_resolve_locals owner names) name = SOME (owner ++ [name])
Proof
  Induct_on `names` >> simp[source_resolve_locals_def] >>
  rw[] >> gvs[source_resolve_locals_def]
QED

Theorem source_resolve_lexical_append:
  source_resolve_lexical scopes name = SOME path ==>
  source_resolve_lexical (scopes ++ outer) name = SOME path
Proof
  Induct_on `scopes` >> simp[source_resolve_lexical_def] >>
  Cases_on `ALOOKUP h name` >> simp[]
QED

Theorem source_resolve_alias_lookup:
  !fuel table path canonical kind.
    source_resolve_alias fuel table path = SOME (canonical,kind) ==>
    ALOOKUP table canonical = SOME kind /\
    (!target. kind <> SR_Alias target)
Proof
  Induct >> simp[source_resolve_alias_def] >> rpt gen_tac >>
  Cases_on `ALOOKUP table path` >> simp[] >>
  rename1 `ALOOKUP table path = SOME binding` >> Cases_on `binding` >>
  strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem source_resolve_members_lookup:
  !names base binding canonical kind.
    ALOOKUP table base = SOME binding /\
    (!target. binding <> SR_Alias target) /\
    source_resolve_members fuel table (base,binding) names = SOME (canonical,kind) ==>
    ALOOKUP table canonical = SOME kind /\
    (!target. kind <> SR_Alias target)
Proof
  Induct >> simp[source_resolve_members_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on `member` >>
  imp_res_tac source_resolve_alias_lookup >>
  first_x_assum irule >> qexistsl_tac [`member0`,`member1`] >> simp[]
QED

Theorem source_resolve_name_lookup:
  source_resolve_name scopes table names = SOME (path,kind) ==>
  ALOOKUP table path = SOME kind /\ (!target. kind <> SR_Alias target)
Proof
  Cases_on `names` >> simp[source_resolve_name_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> PairCases_on `resolved` >>
  imp_res_tac source_resolve_alias_lookup >>
  drule_all source_resolve_members_lookup >> simp[]
QED

Theorem source_resolve_members_nonmodule:
  kind <> SR_Module ==>
  source_resolve_members fuel table (path,kind) (name::names) = NONE
Proof
  simp[source_resolve_members_def]
QED

Theorem source_resolve_builtin_identity:
  source_resolve_callee scopes table (SCE_Name names) args kws =
    SOME (SCE_Builtin b args' kws') <=>
  args' = args /\ kws' = kws /\
  ?path. source_resolve_name scopes table names = SOME (path,SR_Builtin b)
Proof
  simp[source_resolve_callee_def] >>
  Cases_on `source_resolve_name scopes table names` >> simp[] >>
  rename1 `source_resolve_name scopes table names = SOME resolved` >>
  PairCases_on `resolved` >>
  Cases_on `resolved1` >> simp[] >> metis_tac[]
QED

Theorem source_resolve_literal_preserved:
  source_resolve_candidate scopes table (SX_Literal lit) = SOME (SCE_Literal lit)
Proof
  simp[source_resolve_candidate_def, source_constant_candidate_def,
       source_resolve_expr_def]
QED

Theorem source_resolve_rejects_claimed_tags:
  source_resolve_expr scopes table pos (SCE_Builtin b args kws) = NONE /\
  source_resolve_expr scopes table pos (SCE_BytesType fixed bound) = NONE
Proof
  simp[source_resolve_expr_def]
QED

Theorem source_resolve_collect_every:
  !xs ys. source_resolve_collect xs = SOME ys ==>
    (EVERY P ys <=> EVERY (\x. case x of NONE => F | SOME y => P y) xs)
Proof
  Induct >> simp[source_resolve_collect_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[] >>
  Cases_on `source_resolve_collect xs` >> simp[] >>
  strip_tac >> gvs[] >> res_tac >> simp[]
QED

Theorem source_resolve_collect_length:
  !xs ys. source_resolve_collect xs = SOME ys ==> LENGTH ys = LENGTH xs
Proof
  Induct >> simp[source_resolve_collect_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[] >>
  Cases_on `source_resolve_collect xs` >> simp[] >>
  strip_tac >> gvs[] >> res_tac >> simp[]
QED

Theorem source_resolve_claim_actual_import:
  source_resolve_claim_ok registry (SourceImportClaim owner imp target id) ==>
  ?module_syntax. ALOOKUP registry owner = SOME module_syntax /\
    MEM imp (source_resolve_imports module_syntax) /\
    source_resolve_import_target owner imp = SOME target /\
    IS_SOME (ALOOKUP registry target)
Proof
  simp[source_resolve_claim_ok_def] >>
  Cases_on `ALOOKUP registry owner` >> simp[]
QED

Theorem source_resolve_claims_no_id_collision:
  source_resolve_claims_ok registry claims /\ MEM a claims /\ MEM b claims /\
  source_resolve_claim_id a = source_resolve_claim_id b ==>
  source_resolve_claim_target a = source_resolve_claim_target b
Proof
  simp[source_resolve_claims_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem source_resolve_registry_unique:
  source_resolve_registry_ok registry ==>
  ALL_DISTINCT (MAP FST (source_resolve_table registry))
Proof
  simp[source_resolve_registry_ok_def]
QED

Theorem source_resolve_collect_map_every:
  !xs ys. (!x y. MEM x xs /\ f x = SOME y ==> P y) /\
    source_resolve_collect (MAP f xs) = SOME ys ==> EVERY P ys
Proof
  Induct >> simp[source_resolve_collect_def] >> rpt gen_tac >>
  Cases_on `f h` >> simp[] >>
  Cases_on `source_resolve_collect (MAP f xs)` >> simp[] >>
  strip_tac >> gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem source_resolve_atom_names:
  ALOOKUP table path = SOME kind ==>
  EVERY (\p. ALOOKUP table p = SOME SR_Constant)
    (source_const_names (source_resolve_atom pos (path,kind)))
Proof
  Cases_on `kind` >> simp[source_resolve_atom_def, source_const_names_def] >>
  Cases_on `pos` >> simp[source_const_names_def]
QED

Theorem source_resolve_collect_map:
  source_resolve_collect (MAP f xs) = SOME ys ==>
  (!x y. MEM x xs /\ f x = SOME y ==> P y) ==> EVERY P ys
Proof
  metis_tac[source_resolve_collect_map_every]
QED

Theorem source_resolve_name_atom_names:
  source_resolve_name scopes table names = SOME resolved ==>
  EVERY (\p. ALOOKUP table p = SOME SR_Constant)
    (source_const_names (source_resolve_atom pos resolved))
Proof
  PairCases_on `resolved` >> strip_tac >>
  imp_res_tac source_resolve_name_lookup >>
  irule source_resolve_atom_names >> simp[]
QED

Theorem source_resolve_callee_names:
  source_resolve_callee scopes table (SCE_Name names) args kws = SOME resolved /\
  EVERY (\e. EVERY (\p. ALOOKUP table p = SOME SR_Constant) (source_const_names e)) args /\
  EVERY (\kw. EVERY (\p. ALOOKUP table p = SOME SR_Constant)
    (source_const_names (SND kw))) kws ==>
  EVERY (\p. ALOOKUP table p = SOME SR_Constant) (source_const_names resolved)
Proof
  simp[source_resolve_callee_def] >>
  Cases_on `source_resolve_name scopes table names` >> simp[] >>
  rename1 `source_resolve_name scopes table names = SOME binding` >>
  PairCases_on `binding` >> Cases_on `binding1` >>
  simp[source_const_names_def, EVERY_FLAT, EVERY_MAP] >>
  strip_tac >> gvs[] >>
  imp_res_tac source_resolve_name_atom_names >>
  gvs[source_const_names_def, source_resolve_atom_def, EVERY_FLAT, EVERY_MAP]
QED

Theorem source_resolve_keywords_every:
  source_resolve_collect
    (MAP (\(k,v). OPTION_MAP (\r. (k,r))
      (source_resolve_expr scopes table (k = "output_type") v)) kws) = SOME resolved ==>
  (!k v r. MEM (k,v) kws /\
    source_resolve_expr scopes table (k = "output_type") v = SOME r ==> P r) ==>
  EVERY (\kw. P (SND kw)) resolved
Proof
  strip_tac >> strip_tac >> drule source_resolve_collect_map >>
  disch_then irule >> Cases >> simp[] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem source_resolve_call_names:
  !callee args kws.
  (!scopes table pos resolved.
    source_resolve_expr scopes table pos callee = SOME resolved ==>
    EVERY (\p. ALOOKUP table p = SOME SR_Constant) (source_const_names resolved)) /\
  EVERY (\e. !scopes table pos resolved.
    source_resolve_expr scopes table pos e = SOME resolved ==>
    EVERY (\p. ALOOKUP table p = SOME SR_Constant) (source_const_names resolved)) args /\
  EVERY (\kw. !scopes table pos resolved.
    source_resolve_expr scopes table pos (SND kw) = SOME resolved ==>
    EVERY (\p. ALOOKUP table p = SOME SR_Constant) (source_const_names resolved)) kws ==>
  !scopes table pos resolved.
    source_resolve_expr scopes table pos (SCE_Call callee args kws) = SOME resolved ==>
    EVERY (\p. ALOOKUP table p = SOME SR_Constant) (source_const_names resolved)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp_tac (srw_ss()) [Once source_resolve_expr_def, ETA_THM] >>
  Cases_on `source_resolve_collect (MAP (\a. source_resolve_expr scopes table F a) args)` >> simp[] >>
  rename1 `source_resolve_collect (MAP (\a. source_resolve_expr scopes table F a) args) = SOME resolved_args` >>
  Cases_on `source_resolve_collect (MAP (\(k,v). OPTION_MAP (\v'. (k,v'))
    (source_resolve_expr scopes table (k = "output_type") v)) kws)` >> simp[] >>
  rename1 `source_resolve_collect (MAP (\(k,v). OPTION_MAP (\v'. (k,v'))
    (source_resolve_expr scopes table (k = "output_type") v)) kws) = SOME resolved_kws` >>
  `EVERY (\e. EVERY (\p. ALOOKUP table p = SOME SR_Constant)
    (source_const_names e)) resolved_args` by
    (qpat_assum `source_resolve_collect (MAP _ args) = SOME resolved_args`
       (mp_tac o GEN_ALL o MATCH_MP source_resolve_collect_map) >>
     disch_then irule >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\kw. EVERY (\p. ALOOKUP table p = SOME SR_Constant)
    (source_const_names (SND kw))) resolved_kws` by
    (drule source_resolve_keywords_every >>
     disch_then (qspec_then `\e. EVERY (\p. ALOOKUP table p = SOME SR_Constant)
       (source_const_names e)` mp_tac) >> simp[] >>
     disch_then irule >> gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  Cases_on `callee` >> simp[] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  FIRST [drule_all source_resolve_callee_names >> simp[],
    gvs[source_const_names_def, EVERY_FLAT, EVERY_MAP] >> metis_tac[]]
QED

Triviality source_resolve_keyword_induction_every:
  (!expr. (?kw. expr = SND kw /\ MEM kw kws) ==> P expr) <=>
  EVERY (\kw. P (SND kw)) kws
Proof
  simp[EVERY_MEM] >> metis_tac[]
QED

(* Normalize the generated nested induction to the usual EVERY interface. *)
val source_resolve_induction = source_const_expr_induction
  |> SIMP_RULE (srw_ss())
       [setSND_def, source_resolve_keyword_induction_every, GSYM EVERY_MEM];

Theorem source_resolve_expr_names:
  !expr scopes table pos resolved.
    source_resolve_expr scopes table pos expr = SOME resolved ==>
    EVERY (\path. ALOOKUP table path = SOME SR_Constant)
      (source_const_names resolved)
Proof
  ho_match_mp_tac source_resolve_induction >> rpt conj_tac
  >- simp[source_resolve_expr_def, source_const_names_def]
  >- (rpt gen_tac >> gvs[source_resolve_expr_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >> drule source_resolve_name_atom_names >> simp[])
  >- simp[source_resolve_expr_def, source_const_names_def]
  >- simp[source_resolve_expr_def]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      gvs[source_resolve_expr_def, AllCaseEqs()] >>
      strip_tac >> gvs[source_const_names_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      gvs[source_resolve_expr_def, source_resolve_two_def, AllCaseEqs()] >>
      strip_tac >> gvs[source_const_names_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      gvs[source_resolve_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[source_const_names_def, EVERY_FLAT, EVERY_MAP] >>
      drule source_resolve_collect_map >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      gvs[source_resolve_expr_def, source_resolve_two_def, AllCaseEqs()] >>
      strip_tac >> gvs[source_const_names_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      gvs[source_resolve_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[source_const_names_def, EVERY_FLAT, EVERY_MAP] >>
      drule source_resolve_collect_map >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      gvs[source_resolve_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[source_const_names_def, EVERY_FLAT, EVERY_MAP] >>
      drule source_resolve_collect_map >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `expr` >> Cases_on `pos` >>
      simp_tac (srw_ss()) [Once source_resolve_expr_def, source_resolve_two_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      imp_res_tac source_resolve_name_atom_names >>
      gvs[source_const_names_def] >> metis_tac[])
  >- simp[source_resolve_expr_def]
  >- ACCEPT_TAC source_resolve_call_names
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      gvs[source_resolve_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[source_const_names_def, EVERY_FLAT, EVERY_MAP] >>
      drule source_resolve_collect_map >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
QED

Theorem source_resolve_declarations_preserves_identities:
  !declarations resolved.
    source_resolve_declarations scopes table declarations = SOME resolved ==>
    MAP FST resolved = MAP FST declarations
Proof
  Induct >> simp[source_resolve_declarations_def, source_resolve_collect_def] >>
  Cases_on `h` >> simp[] >> rpt gen_tac >>
  rename1 `source_resolve_candidate scopes table init` >>
  Cases_on `source_resolve_candidate scopes table init` >> simp[] >>
  Cases_on `source_resolve_collect
    (MAP (\(path,expr). OPTION_MAP (\resolved. (path,resolved))
      (source_resolve_candidate scopes table expr)) declarations)` >> simp[] >>
  strip_tac >> gvs[source_resolve_declarations_def] >> res_tac >> simp[]
QED

Theorem source_resolve_program_registry_preserves_modules:
  source_resolve_program_registry (SourceProgram main imports) keys = SOME registry ==>
  MAP SND registry = main::imports
Proof
  simp[source_resolve_program_registry_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> simp[MAP_ZIP]
QED

Theorem source_resolve_fixed_bytes_identity:
  source_resolve_atom pos resolved = SCE_BytesType fixed bound ==>
  ?path width. resolved = (path,SR_FixedBytes width) /\ pos /\ fixed /\
    bound = SCE_Literal (SCL_Int (&width))
Proof
  PairCases_on `resolved` >> Cases_on `resolved1` >>
  simp[source_resolve_atom_def] >> Cases_on `pos` >> simp[] >> metis_tac[]
QED

Theorem source_resolve_bytes_bound_identity:
  source_resolve_expr scopes table T (SCE_Subscript (SCE_Name names) index) =
    SOME (SCE_BytesType F bound) ==>
  ?path. source_resolve_name scopes table names = SOME (path,SR_Bytes) /\
    source_resolve_expr scopes table F index = SOME bound
Proof
  simp[Once source_resolve_expr_def] >>
  Cases_on `source_resolve_name scopes table names` >> simp[] >>
  rename1 `source_resolve_name scopes table names = SOME resolved` >>
  PairCases_on `resolved` >> Cases_on `resolved1` >>
  simp[source_resolve_two_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem source_resolve_decl_no_builtin:
  !owner decl path b.
    ~MEM (path,SR_Builtin b) (source_resolve_decl_bindings owner decl)
Proof
  Cases_on `decl` >>
  simp[source_resolve_decl_bindings_def, MEM_FLAT, MEM_MAP] >>
  rpt gen_tac >> CCONTR_TAC >> gvs[AllCaseEqs()]
QED

Theorem source_resolve_module_no_builtin:
  ~MEM (path,SR_Builtin b) (source_resolve_module_bindings owner module_syntax)
Proof
  Cases_on `module_syntax` >>
  simp[source_resolve_module_bindings_def, MEM_FLAT, MEM_MAP] >>
  metis_tac[source_resolve_decl_no_builtin]
QED

Theorem source_resolve_table_builtin_identity:
  ALOOKUP (source_resolve_table registry) path = SOME (SR_Builtin b) ==>
  MEM (path,SR_Builtin b) source_resolve_prelude
Proof
  strip_tac >> drule ALOOKUP_MEM >>
  simp[source_resolve_table_def, MEM_FLAT, MEM_MAP] >>
  strip_tac >> gvs[] >>
  gvs[MEM_MAP, FORALL_PROD] >> PairCases_on `y` >> gvs[] >>
  metis_tac[source_resolve_module_no_builtin]
QED

Theorem source_resolve_module_expr_names:
  source_resolve_module_expr registry owner expr = SOME resolved ==>
  EVERY (\path. ALOOKUP (source_resolve_table registry) path = SOME SR_Constant)
    (source_const_names resolved)
Proof
  simp[source_resolve_module_expr_def, AllCaseEqs()] >> strip_tac >>
  drule source_resolve_expr_names >> simp[]
QED
