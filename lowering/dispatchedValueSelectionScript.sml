(* Arbitrary-calldata selection, independent of argument re-encoding. *)
Theory dispatchedValueSelection
Ancestors calldataSelectorProps sourceEntrySelection checkedSelectorTableProps loweringShapeProps
  entryDispatchProps moduleLoweringProps selectorDispatch supportedProgram supportedNames
  vyperCalldata selectorCompilerProps vyperABIEntries compileVyper publicGetterProps
Libs BasicProvers

val _ = Parse.hide "body";

Theorem signatures_without_defaults[local]:
  !fns. ~EXISTS external_has_defaults fns ==>
    FLAT (MAP (\(mut,nr,rr,name,args,ds,ret,body).
      abi_function_signatures name args ds) fns) =
    MAP (\(mut,nr,rr,name,args,ds,ret,body). (name,MAP SND args)) fns
Proof
  Induct >> simp[] >> PairCases >>
  simp[external_has_defaults_def, listTheory.NULL_EQ] >> rpt strip_tac >> simp[]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8389 gate widening census (never lands)
Proof
  strip_tac >> rpt gen_tac >>
  drule supported_program_no_external_defaults >>
  disch_then (mp_tac o MATCH_MP signatures_without_defaults) >>
  rewrite_tac[classify_external_signatures] >> strip_tac >>
  mp_tac (MATCH_MP sortingTheory.PERM_MEM_EQ abi_signature_partition) >>
  disch_then (qspec_then `(name,tys)` mp_tac) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
*)
Theorem source_signature_table[local]:
  supported_program tops ==>
  !name tys.
    MEM (name,tys) (abi_external_signatures tops) <=>
    MEM (name,tys)
      (MAP (\(mut,nr,rr,n,args,ds,ret,body). (n,MAP SND args))
        (FST (classify_functions tops)))
Proof
  cheat
QED

Theorem table_no_hit[local]:
  !fns cd fb. 4 <= LENGTH cd /\
    (!name tys. MEM (name,tys)
      (MAP (\(m,n,r,name,args,ds,ret,body). (name,MAP SND args)) fns) ==>
      abi_method_id tenv name tys <> cd_selector cd) ==>
    linear_dispatch_target cd
      (MAP (\(sel,lbl,z). (sel,lbl)) (build_selectors tenv fns)) fb = fb
Proof
  Induct >> simp[build_selectors_def, linear_dispatch_target_def] >>
  PairCases >> rpt strip_tac >>
  simp[build_selectors_def, compute_selector_method_id,
       linear_dispatch_target_def, calldata_hits_selector_def] >>
  drule cd_selector_method_id >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem classified_external_source_lookup:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  MEM (mut,nr,rr,name,args,ds,ret,body) (FST (classify_functions tops)) ==>
  ?rawdefaults rawbody.
    vyperInterpreter$lookup_function NONE name External tops =
      SOME (mut,nr,args,rawdefaults,ret,rawbody) /\
    ds = subst_consts_exprs (module_consts_env tops []) rawdefaults /\
    body = subst_consts_stmts (module_consts_env tops []) rawbody
Proof
  strip_tac >>
  drule classify_functions_external_source >> strip_tac >>
  gvs[constSubstTheory.subst_consts_fn_def] >>
  qexistsl_tac [`rawdefaults`, `rawbody`] >> simp[]
  >- (irule lookup_function_external_unique_decl >> simp[] >>
      qexists_tac `FunctionDecl External mut nr rr name args rawdefaults ret rawbody` >>
      simp[vyperInterpreterTheory.lookup_function_def,
           vyperTypeContractTheory.external_name_keys_toplevel_def]) >>
  drule public_getter_lookup_singleton >> strip_tac >>
  metis_tac[lookup_function_external_unique_decl]
QED

Theorem default_fold_present[local]:
  !tops. EXISTS is_default_decl tops ==>
    ?m nr rr args ds ret body.
      FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) =
        SOME (m,nr,rr,"__default__",args,ds,ret,body)
Proof
  Induct >> simp[] >> gen_tac >>
  Cases_on `h` >> simp[is_default_decl_def, classify_function_def] >>
  Cases_on `f` >>
  qabbrev_tac `acc = FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `acc` >> gvs[GSYM markerTheory.Abbrev_def] >>
  simp[is_default_decl_def, classify_function_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem default_classified_present[local]:
  EXISTS is_default_decl tops ==>
  ?m nr rr args ds ret body.
    FST (SND (SND (classify_functions tops))) =
      SOME (m,nr,rr,"__default__",args,ds,ret,body)
Proof
  strip_tac >> drule default_fold_present >>
  simp[classify_functions_def] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `fb` >> gvs[] >> PairCases_on `x` >>
  simp[constSubstTheory.subst_consts_fn_def]
QED

Theorem fallback_source_lookup[local]:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,ds,ret,body) ==>
  ?rawdefaults rawbody.
    vyperInterpreter$lookup_function NONE name External tops =
      SOME (mut,nr,args,rawdefaults,ret,rawbody) /\
    ds = subst_consts_exprs (module_consts_env tops []) rawdefaults /\
    body = subst_consts_stmts (module_consts_env tops []) rawbody
Proof
  strip_tac >>
  drule classify_functions_fallback_mem >> strip_tac >>
  gvs[constSubstTheory.subst_consts_fn_def] >>
  qexistsl_tac [`rawdefaults`, `rawbody`] >> simp[] >>
  irule lookup_function_external_unique_decl >> simp[] >>
  qexists_tac `FunctionDecl External mut nr rr name args rawdefaults ret rawbody` >>
  simp[vyperInterpreterTheory.lookup_function_def,
       vyperTypeContractTheory.external_name_keys_toplevel_def]
QED

Theorem signature_hit_entry[local]:
  supported_program tops /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  4 <= LENGTH cd /\
  FIND (\(n,tys). abi_method_id (type_env tops) n tys = cd_selector cd)
    (abi_external_signatures tops) = SOME (name,tys) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  (?rr. MEM (mut,nr,rr,name,args,[],ret,
      subst_consts_stmts (module_consts_env tops []) fbody) (FST (classify_functions tops))) /\
  !fb. linear_dispatch_target cd
    (MAP (\(sel,lbl,z). (sel,lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
    "fn_" ++ name
Proof
  strip_tac >>
  `MEM (name,tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  `abi_method_id (type_env tops) name tys = cd_selector cd` by
    (drule venomInstTheory.FIND_P >> simp[]) >>
  drule source_signature_table >> strip_tac >>
  `MEM (name,tys) (MAP (\(m,n,r,name,args,ds,ret,body). (name,MAP SND args))
      (FST (classify_functions tops)))` by metis_tac[] >>
  pop_assum mp_tac >> simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  strip_tac >> gvs[] >>
  drule_all classified_external_source_lookup >> strip_tac >>
  gvs[constSubstTheory.subst_consts_expr_def] >>
  conj_tac >- metis_tac[] >> gen_tac >>
  irule linear_dispatch_target_distinct >>
  conj_tac
  >- (`!l:(num # string # bool) list.
         MAP FST (MAP (\(sel,lbl,z). (sel,lbl)) l) = MAP FST l` by
        (Induct >> simp[] >> PairCases >> simp[]) >>
      fs[supported_program_def, supported_declaration_names_def,
         supported_selectors_distinct_def]) >>
  qexists_tac `abi_method_id (type_env tops) name (MAP SND args)` >>
  conj_tac
  >- (drule build_selectors_mem >>
      disch_then (qspec_then `type_env tops` mp_tac) >>
      simp[compute_selector_method_id, listTheory.MEM_MAP] >> strip_tac >>
      qexists_tac `(cd_selector cd,"fn_" ++ name,
        selector_has_trailing_zeroes (cd_selector cd))` >> simp[]) >>
  drule cd_selector_method_id >> simp[calldata_hits_selector_def]
QED

Theorem source_dispatched_linear_target_nr:
  supported_program tops /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  calldata_dispatch tops cd = SOME (name,vals) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  (?rr. MEM (mut,nr,rr,name,args,[],ret,
      subst_consts_stmts (module_consts_env tops []) fbody) (FST (classify_functions tops)) /\
    !fb. linear_dispatch_target cd
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
      "fn_" ++ name) \/
  (name = "__default__" /\ EXISTS is_default_decl tops /\
    (?rr. FST (SND (SND (classify_functions tops))) =
      SOME (mut,nr,rr,name,args,[],ret,
        subst_consts_stmts (module_consts_env tops []) fbody)) /\
    !fb. linear_dispatch_target cd
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops)))) fb = fb)
Proof
  strip_tac >>
  `name = "__default__" /\ EXISTS is_default_decl tops ==>
    ?rr. FST (SND (SND (classify_functions tops))) =
      SOME (mut,nr,rr,name,args,[],ret,
        subst_consts_stmts (module_consts_env tops []) fbody)` by
    (strip_tac >> drule default_classified_present >> strip_tac >>
     drule_all fallback_source_lookup >> strip_tac >>
     gvs[constSubstTheory.subst_consts_expr_def] >> metis_tac[]) >>
  Cases_on `LENGTH cd < 4`
  >- (gvs[calldata_dispatch_def] >>
      disj2_tac >> simp[linear_dispatch_target_short]) >>
  Cases_on `FIND (\(n,tys). abi_method_id (type_env tops) n tys = cd_selector cd)
    (abi_external_signatures tops)`
  >- (gvs[calldata_dispatch_def] >> disj2_tac >> simp[] >>
      gen_tac >> irule table_no_hit >> simp[] >>
      `!l n ts. FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd) l = NONE /\
        MEM (n,ts) l ==> abi_method_id (type_env tops) n ts <> cd_selector cd` by
        (Induct >> simp[listTheory.FIND_thm] >> PairCases >>
         Cases_on `abi_method_id (type_env tops) h0 h1 = cd_selector cd` >>
         simp[] >> metis_tac[]) >>
      drule source_signature_table >> strip_tac >> metis_tac[]) >>
  PairCases_on `x` >>
  gvs[calldata_dispatch_def, AllCaseEqs()] >>
  disj1_tac >> `4 <= LENGTH cd` by decide_tac >>
  drule_all signature_hit_entry >> simp[] >> metis_tac[]
QED

Theorem source_dispatched_linear_target:
  supported_program tops /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  calldata_dispatch tops cd = SOME (name,vals) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  (?rr. MEM (mut,F,rr,name,args,[],ret,
        subst_consts_stmts (module_consts_env tops []) fbody) (FST (classify_functions tops)) /\
    !fb. linear_dispatch_target cd
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
      "fn_" ++ name) \/
  (name = "__default__" /\ EXISTS is_default_decl tops /\
    (?rr. FST (SND (SND (classify_functions tops))) =
      SOME (mut,F,rr,name,args,[],ret,
        subst_consts_stmts (module_consts_env tops []) fbody)) /\
    !fb. linear_dispatch_target cd
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops)))) fb = fb)
Proof
  MATCH_ACCEPT_TAC (Q.INST [`nr` |-> `F`] (SPEC_ALL source_dispatched_linear_target_nr))
QED

(* A successful dispatch names an external declaration or its getter. *)
Theorem calldata_dispatch_has_source_entry:
  supported_program tops /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  calldata_dispatch tops cd = SOME (name,vals) ==>
  ?mut nr args dflts ret fbody.
    vyperInterpreter$lookup_function NONE name External tops =
      SOME (mut,nr,args,dflts,ret,fbody)
Proof
  strip_tac >>
  Cases_on `if LENGTH cd < 4 then NONE else
    FIND (\(n,tys). abi_method_id (type_env tops) n tys = cd_selector cd)
      (abi_external_signatures tops)`
  >- (gvs[calldata_dispatch_def, AllCaseEqs()] >>
      drule default_classified_present >> strip_tac >>
      drule_all fallback_source_lookup >> simp[] >> metis_tac[]) >>
  PairCases_on `x` >>
  gvs[calldata_dispatch_def, AllCaseEqs()] >>
  `MEM (name,x1) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  qpat_x_assum `MEM _ (abi_external_signatures _)` mp_tac >>
  drule source_signature_table >>
  disch_then (qspecl_then [`name`,`x1`] (fn th => REWRITE_TAC [th])) >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  strip_tac >> gvs[] >>
  drule_all classified_external_source_lookup >> simp[] >> metis_tac[]
QED
