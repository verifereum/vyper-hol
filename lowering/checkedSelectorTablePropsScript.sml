(* The checker supplies distinct IDs for the actual grouped dispatch table,
   including every default-argument prefix. Getter signatures remain part of
   the checked superset even before getter lowering is enabled. *)
Theory checkedSelectorTableProps
Ancestors
  publicGetterProps
  selectorCompilerProps compileVyper moduleLowering vyperTypeContract
  vyperABIEntries vyperContext finite_map list rich_list
Libs
  BasicProvers

Definition explicit_external_decl_def:
  explicit_external_decl
    (FunctionDecl External mut nr rr name args dflts ret stmts) =
      (name <> "__default__") /\
  explicit_external_decl _ = F
End

Theorem classify_function_external_component:
  FST (classify_function top acc) =
    case top of
      FunctionDecl External mut nr rr name args dflts ret stmts =>
        if name = "__default__" then FST acc
        else (mut,nr,rr,name,args,dflts,ret,stmts)::FST acc
    | _ => FST acc
Proof
  PairCases_on `acc` >> Cases_on `top` >> simp[classify_function_def] >>
  every_case_tac >> simp[]
QED

Theorem signature_subst_consts[local]:
  (\(mut,nr,rr,name,args,dflts,ret,stmts).
    abi_function_signatures name args dflts) (subst_consts_fn env fn) =
  (\(mut,nr,rr,name,args,dflts,ret,stmts).
    abi_function_signatures name args dflts) fn
Proof
  `!es. LENGTH (subst_consts_exprs env es) = LENGTH es` by
    (Induct >> simp[constSubstTheory.subst_consts_expr_def]) >>
  PairCases_on `fn` >>
  simp[constSubstTheory.subst_consts_fn_def, abi_function_signatures_def,
       abi_entries_def]
QED

Theorem fold_external_signatures[local]:
  FLAT (MAP (\(mut,nr,rr,name,args,dflts,ret,stmts).
    abi_function_signatures name args dflts)
    (FST (FOLDR classify_function ([],[],NONE,NONE) tops))) =
  FLAT (MAP abi_decl_signatures (FILTER explicit_external_decl tops))
Proof
  Induct_on `tops` >> simp[] >> gen_tac >>
  simp[classify_function_external_component] >>
  Cases_on `h` >> simp[explicit_external_decl_def, abi_decl_signatures_def] >>
  every_case_tac >> gvs[explicit_external_decl_def, abi_decl_signatures_def]
QED

Theorem public_getter_present[local]:
  IS_SOME (public_getter top) =
  (case top of
     VariableDecl (Public nr) mut name ty slot => T
   | HashMapDecl (Public nr) tr name kt vt slot => T
   | _ => F)
Proof
  Cases_on `top` >> simp[public_getter_def] >>
  Cases_on `v` >> simp[public_getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt IF_CASES_TAC >> simp[] >> rpt (pairarg_tac >> gvs[])
QED
Theorem getter_signature_component[local]:
  FLAT (MAP (\(mut,nr,rr,name,args,dflts,ret,stmts).
    abi_function_signatures name args dflts)
    (case public_getter top of NONE => [] | SOME g => [g])) =
  if IS_SOME (public_getter top) then abi_decl_signatures top else []
Proof
  Cases_on `public_getter top` >>
  qpat_assum `public_getter _ = _` (mp_tac o Q.AP_TERM `IS_SOME`) >>
  simp[public_getter_present] >> strip_tac >> gvs[] >>
  rename1 `public_getter top = SOME g` >> PairCases_on `g` >>
  drule public_getter_signature >> drule public_getter_defaults >>
  simp[abi_function_signatures_def]
QED

Theorem getter_external_signatures[local]:
  FLAT (MAP (\(mut,nr,rr,name,args,dflts,ret,stmts).
    abi_function_signatures name args dflts) (public_getters tops)) =
  FLAT (MAP abi_decl_signatures (FILTER (IS_SOME o public_getter) tops))
Proof
  Induct_on `tops` >> simp[public_getters_def] >> qx_gen_tac `top` >>
  rewrite_tac[getter_signature_component] >>
  simp[combinTheory.o_DEF, public_getter_present] >>
  rpt CASE_TAC >> simp[]
QED
Theorem classify_external_signatures:
  FLAT (MAP (\(mut,nr,rr,name,args,dflts,ret,stmts).
      abi_function_signatures name args dflts)
    (FST (classify_functions tops))) =
  FLAT (MAP abi_decl_signatures (FILTER explicit_external_decl tops)) ++
  FLAT (MAP abi_decl_signatures (FILTER (IS_SOME o public_getter) tops))
Proof
  simp[classify_functions_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF, signature_subst_consts, SF ETA_ss] >>
  mp_tac fold_external_signatures >>
  asm_rewrite_tac[] >> disch_then (fn th => rewrite_tac[th]) >>
  simp[getter_external_signatures, combinTheory.o_DEF, public_getter_present]
QED

Theorem mem_flat_map_filter:
  MEM e (FLAT (MAP f (FILTER P xs))) ==> MEM e (FLAT (MAP f xs))
Proof
  Induct_on `xs` >> simp[] >> qx_gen_tac `item` >> Cases_on `P item` >>
  simp[] >> metis_tac[]
QED

Theorem all_distinct_flat_map_filter:
  ALL_DISTINCT (FLAT (MAP f xs)) ==>
  ALL_DISTINCT (FLAT (MAP f (FILTER P xs)))
Proof
  Induct_on `xs` >> simp[] >> qx_gen_tac `item` >> Cases_on `P item` >>
  simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >> fs[] >>
  drule mem_flat_map_filter >> metis_tac[]
QED

Theorem grouped_selector_method_ids:
  MAP FST (grouped_selectors
    (MAP (package_external_group tops target trans nkeys)
      (FST (classify_functions tops)))) =
  FLAT (MAP (\top. MAP (\(name,tys). abi_method_id (type_env tops) name tys)
    (abi_decl_signatures top)) (FILTER explicit_external_decl tops)) ++
  FLAT (MAP (\top. MAP (\(name,tys). abi_method_id (type_env tops) name tys)
    (abi_decl_signatures top)) (FILTER (IS_SOME o public_getter) tops))
Proof
  `(\func. MAP FST (external_group_selectors
      (package_external_group tops target trans nkeys func))) =
    (\(mut,nr,rr,name,args,dflts,ret,stmts).
      MAP (\(name,tys). abi_method_id (type_env tops) name tys)
        (abi_function_signatures name args dflts))` by
    simp[FUN_EQ_THM, pairTheory.FORALL_PROD, external_group_method_ids] >>
  mp_tac (AP_TERM
    ``MAP (\(name,tys). abi_method_id (type_env tops) name tys)``
    classify_external_signatures) >>
  fs[grouped_selectors_def, listTheory.MAP_FLAT, MAP_MAP_o,
       combinTheory.o_DEF] >> strip_tac >>
  qpat_x_assum `FLAT _ = _ ++ _`
    (fn th => CONV_TAC (RAND_CONV (REWR_CONV (SYM th)))) >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[pairTheory.FORALL_PROD]
QED

Theorem abi_signature_partition[local]:
  PERM (FLAT (MAP abi_decl_signatures (FILTER explicit_external_decl tops)) ++
        FLAT (MAP abi_decl_signatures (FILTER (IS_SOME o public_getter) tops)))
       (abi_external_signatures tops)
Proof
  Induct_on `tops` >> simp[abi_external_signatures_def] >> qx_gen_tac `top` >>
  Cases_on `top`
  >- (Cases_on `f` >>
      Cases_on `s = "__default__"` >>
      gvs[explicit_external_decl_def, public_getter_present, combinTheory.o_DEF,
          abi_decl_signatures_def, abi_external_signatures_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, sortingTheory.PERM_APPEND_IFF] >>
      asm_rewrite_tac[]) >>
  simp[explicit_external_decl_def, public_getter_present, combinTheory.o_DEF,
       abi_decl_signatures_def] >>
  every_case_tac >> gvs[explicit_external_decl_def, abi_decl_signatures_def,
                       public_getter_present, combinTheory.o_DEF,
                       abi_external_signatures_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, sortingTheory.PERM_APPEND_IFF] >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[sortingTheory.PERM_SYM] >>
  irule sortingTheory.CONS_PERM >>
  metis_tac[sortingTheory.PERM_SYM]
QED

Theorem grouped_selectors_distinct:
  ALL_DISTINCT (abi_external_method_ids (type_env tops) tops) ==>
  ALL_DISTINCT (MAP FST (grouped_selectors
    (MAP (package_external_group tops target trans nkeys)
      (FST (classify_functions tops)))))
Proof
  strip_tac >> simp[grouped_selector_method_ids] >>
  mp_tac (Q.ISPEC `\(name,tys). abi_method_id (type_env tops) name tys`
    (MATCH_MP sortingTheory.PERM_MAP abi_signature_partition)) >>
  disch_then (mp_tac o MATCH_MP sortingTheory.ALL_DISTINCT_PERM) >>
  gvs[abi_external_method_ids_def, listTheory.MAP_FLAT, MAP_MAP_o,
      combinTheory.o_DEF, public_getter_present]
QED

Theorem check_contract_grouped_selectors_distinct:
  check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
  ALL_DISTINCT (MAP FST (grouped_selectors
    (MAP (package_external_group tops target trans nkeys)
      (FST (classify_functions tops)))))
Proof
  strip_tac >> irule grouped_selectors_distinct >>
  `type_env_all_modules [(NONE,tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  metis_tac[check_contract_external_method_ids_distinct, MEM]
QED

Theorem grouped_selectors_no_defaults:
  ~EXISTS external_has_defaults fns ==>
  grouped_selectors (MAP (package_external_group tops target trans nkeys) fns) =
    build_selectors (type_env tops) fns
Proof
  Induct_on `fns` >> simp[grouped_selectors_def, build_selectors_def] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >>
  simp[external_has_defaults_def] >> strip_tac >>
  rename1 `NULL defaults` >>
  gvs[NULL_EQ, package_external_group_no_defaults, external_group_selectors_def,
      grouped_selectors_def, build_selectors_def]
QED

Theorem check_contract_selectors_distinct:
  check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) ==>
  ALL_DISTINCT (MAP FST
    (build_selectors (type_env tops) (FST (classify_functions tops))))
Proof
  strip_tac >> drule check_contract_grouped_selectors_distinct >>
  fs[grouped_selectors_no_defaults]
QED
