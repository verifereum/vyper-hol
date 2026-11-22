Theory groupedDefaultSyntax
Ancestors
  constSubstCorrect constSubst constSubstMods loweringShapeSource whitelistCheckerConsts
  whitelistCheckerDecls vyperTypeExternalDefaults vyperTypeContract
  vyperTypeInvariants vyperAST list alist option

Theorem bool_literal_default_substitution[local]:
  bool_literal_expr e ==> bool_literal_expr (subst_consts_expr E e)
Proof
  Cases_on `e` >> simp[bool_literal_expr_def, subst_consts_expr_def]
QED

Theorem runtime_constant_substitution[local]:
  (!E e. runtime_constant_expr mods e /\
    (!id r. ALOOKUP E id = SOME r ==> constant_expr mods r) ==>
    runtime_constant_expr mods (subst_consts_expr E e)) /\
  (!E t. subst_consts_btarget E t = subst_consts_btarget E t) /\
  (!E es. EVERY (runtime_constant_expr mods) es /\
    (!id r. ALOOKUP E id = SOME r ==> constant_expr mods r) ==>
    EVERY (runtime_constant_expr mods) (subst_consts_exprs E es)) /\
  (!E opt. subst_consts_opt E opt = subst_consts_opt E opt) /\
  (!E fs. EVERY (runtime_constant_expr mods) (MAP SND fs) /\
    (!id r. ALOOKUP E id = SOME r ==> constant_expr mods r) ==>
    EVERY (runtime_constant_expr mods) (MAP SND (subst_consts_fields E fs)))
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[runtime_constant_expr_def,subst_consts_expr_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `ns` >> gvs[subst_consts_expr_def,runtime_constant_expr_def] >>
      Cases_on `ALOOKUP E id` >> gvs[runtime_constant_expr_def] >>
      metis_tac[constant_expr_runtime_constant])
  >- (Cases_on `ns` >> gvs[subst_consts_expr_def,runtime_constant_expr_def] >>
      Cases_on `ALOOKUP E id` >> gvs[runtime_constant_expr_def] >>
      metis_tac[constant_expr_runtime_constant]) >>
  metis_tac[bool_literal_default_substitution, subst_consts_constant_expr]
QED

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
  drule_all (cj 3 runtime_constant_substitution) >> simp[]
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
