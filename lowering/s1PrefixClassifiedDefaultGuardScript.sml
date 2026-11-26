Theory s1PrefixClassifiedDefaultGuard
Ancestors
  compileVyper constSubst loweringShapeProps list pair
Libs
  groupedDefaultLoweringGuardLib

Theorem lowered_classified_raw_defaults_no_sha:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  MEM (mut,nr,rr,name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,ss)
    (FST (classify_functions tops)) ==>
  no_sha256_exprs dflts
Proof
  strip_tac >> Cases_on `dflts = []`
  >- simp[no_sha256_collections] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (externals,_,_,_)` >>
  fs[] >>
  `EXISTS external_has_defaults externals` by
    (simp[EXISTS_MEM] >>
     qexists `(mut,nr,rr,name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,ss)` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp_tac bool_ss [external_has_defaults_def,NULL_EQ,GSYM LENGTH_NIL,
                       subst_consts_exprs_length] >> simp[]) >>
  groupedDefaultLoweringGuardLib.raw_defaults_no_sha_tac
    `MEM (mut,nr,rr,name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,ss) externals`
QED
