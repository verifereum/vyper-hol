(* The selected linked constructor comes from the checked main module. *)
Theory linkedDeployConstructorSource
Ancestors
  ctorDeployDefs compileUnit constSubstMods vyperTypeContract
  vyperTypeContractStaticMaps vyperInterpreter list option pair

Theorem linked_deploy_constructor_source:
  check_contract T layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  classify_functions_unit mods exps = (exts,ints,fb,SOME cf,imp_ctors) ==>
  ?mut args body.
    MEM (FunctionDecl Deploy mut F F "__init__" args [] NoneT body) tops /\
    mut <> Pure /\ mut <> View /\
    vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
      SOME (mut,F,args,[],NoneT,body) /\
    cf = (mut,F,F,"__init__",args,[],NoneT,
          subst_consts_stmts_mods (consts_env_mods mods) body)
Proof
  strip_tac >>
  Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
  rename1 `FOLDR classify_function _ tops = classified` >>
  PairCases_on `classified` >>
  qpat_x_assum `classify_functions_unit mods exps = _` mp_tac >>
  simp[classify_functions_unit_def, main_module_def] >>
  Cases_on `classified3` >> simp[] >> strip_tac >>
  rename1 `FOLDR classify_function _ tops = (_,_,_,SOME chosen)` >>
  PairCases_on `chosen` >>
  `MEM (FunctionDecl Deploy chosen0 chosen1 chosen2 chosen3 chosen4 chosen5 chosen6 chosen7) tops` by
    (qspecl_then [`tops`,`chosen0`,`chosen1`,`chosen2`,`chosen3`,`chosen4`,`chosen5`,`chosen6`,`chosen7`]
        mp_tac classify_fold_ctor_mem >>
     simp[]) >>
  `check_toplevel_decl mods art NONE
     (FunctionDecl Deploy chosen0 chosen1 chosen2 chosen3 chosen4 chosen5 chosen6 chosen7)` by
    (irule check_contract_toplevel_decl_MEM_checked >>
     conj_tac
     >- (qexistsl_tac [`addr`,`layouts`,`T`] >> simp[]) >>
     qexists_tac `tops` >> simp[]) >>
  fs[check_toplevel_decl_def, function_header_ok_def, function_mutability_ok_def,
     listTheory.NULL_EQ] >>
  qexistsl_tac [`chosen0`,`chosen4`,`chosen7`] >>
  simp[subst_consts_fn_mods_def, subst_consts_expr_mods_def] >>
  qspecl_then [`tops`,`NONE : num option`,`"__init__"`] mp_tac classify_fold_ctor_lookup >>
  simp[]
QED
