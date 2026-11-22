Theory groupedDefaultSyntax
Ancestors
  constSubstCorrect constSubst constSubstMods loweringShapeSource whitelistCheckerConsts
  runtimeConstantSubstitutionProps
  whitelistCheckerDecls vyperTypeExternalDefaults vyperTypeContract
  vyperTypeInvariants vyperAST list alist option

Theorem grouped_checked_default_syntax:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl External mut nr rr name args dflts ret fbody) tops ==>
  LENGTH dflts <= LENGTH args /\
  MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
  EVERY (runtime_constant_expr [(NONE,tops)]) dflts /\
  EVERY (runtime_constant_expr [(NONE,tops)])
    (subst_consts_exprs (module_consts_env tops []) dflts) /\
  well_typed_exprs (artifact_env art [(NONE,tops)] NONE) dflts /\
  well_typed_exprs (artifact_env art [(NONE,tops)] NONE)
    (subst_consts_exprs (module_consts_env tops []) dflts)
Proof
  strip_tac >>
  `External <> Deploy` by simp[] >>
  drule_all check_contract_single_body >>
  simp[check_function_body_def, defaults_env_function_entry_env,
    subst_consts_mods_singleton, consts_env_mods_singleton] >> strip_tac >>
  `LENGTH dflts <= LENGTH args` by
    (qpat_assum `MAP expr_type dflts = _` (mp_tac o AP_TERM ``LENGTH : type list -> num``) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
    constant_expr [(NONE,tops)] r` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`mode` |-> `F`,`artifact` |-> `art`,`mods` |-> `[(NONE,tops)]`]
       (SPEC_ALL checked_module_consts_env_replacement_constant)) >>
     simp[]) >>
  asm_rewrite_tac[] >>
  fs[subst_consts_exprs_map, EVERY_MAP, combinTheory.o_DEF, EVERY_MEM] >>
  simp[MEM_MAP] >>
  metis_tac[subst_const_runtime_constant]
QED

Theorem grouped_keyword_initializer_specs:
  !kw ds vars.
    LENGTH kw = LENGTH ds /\
    MAP (\(name,_,ty,e). (name,ty,e)) vars =
      MAP (\((name,ty),e). (name,ty,e)) (ZIP (kw,ds)) ==>
    MAP (\(name,_,ty,_). (name,ty)) vars = kw /\
    MAP (\(_,_,_,e). e) vars = ds
Proof
  Induct
  >- (Cases >> Cases >> simp[]) >>
  qx_gen_tac `arg` >> PairCases_on `arg` >>
  Cases >> Cases >> simp[] >>
  PairCases_on `h'` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
