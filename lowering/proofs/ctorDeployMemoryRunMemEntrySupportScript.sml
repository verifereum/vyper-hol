Theory ctorDeployMemoryRunMemEntrySupport
Ancestors
  compileVyper supportedProgram supportedDecls list ctorSourceInputs
  ctorDeployMemoryRunMemEntryFormalBound ctorDeployMemoryRunMemEntryAggregate

Theorem ctor_classified_constructor_member:
  !tops exts ints fb mut nr rr fname fargs dflts ret body.
  classify_functions tops =
    (exts,ints,fb,SOME (mut,nr,rr,fname,fargs,dflts,ret,body)) ==>
  MEM (FunctionDecl Deploy mut nr rr fname fargs dflts ret body) tops
Proof
  Induct_on `tops` >- simp[classify_functions_def] >>
  rpt gen_tac >>
  Cases_on `classify_functions tops` >>
  PairCases_on `r` >>
  fs[classify_functions_def] >>
  Cases_on `h` >> simp[classify_function_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `f` >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ctor_classified_constructor_supported:
  !tops exts ints fb mut nr rr fname fargs dflts ret body.
  supported_program tops /\
  classify_functions tops =
    (exts,ints,fb,SOME (mut,nr,rr,fname,fargs,dflts,ret,body)) ==>
  EVERY (supported_value_type tops) (MAP SND fargs)
Proof
  rpt gen_tac >> strip_tac >> drule ctor_classified_constructor_member >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract] >>
  simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, combinTheory.o_DEF,
    supported_function_argument_def] >> metis_tac[]
QED

Theorem constructor_bound_abi_inputs:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   ce_pack pos_args ce0 imm vals avs scope.
    package_constructor tops use_trans nkey_map
      (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
      (ce_pack,pos_args,mut = Payable,nr,nkey_map fname,use_trans,fbody,ret) /\
    ce0 = (ce_pack with ce_imm_alloca := imm) /\
    contract_namespaces_ok T [((NONE:num option),tops)] /\
    EVERY (assignable_type (type_env tops)) (MAP SND fargs) /\
    ALL_DISTINCT (MAP FST fargs) /\
    bind_arguments (type_env tops) fargs vals = SOME scope /\
    vyper_to_abi_list (type_env tops) (MAP SND fargs) vals = SOME avs /\
    EVERY (supported_value_type tops) (MAP SND fargs) /\
    fn_allocs_ok tops (mut,nr,rr,fname,fargs,dflts,ret,fbody) /\
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ==>
    !i. i < LENGTH fargs ==>
      has_type (vyper_to_abi_type (type_env tops) (SND (EL i fargs))) (EL i avs) /\
      abi_to_vyper (type_env tops) (SND (EL i fargs)) (EL i avs) = SOME (EL i vals)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all constructor_bound_source_inputs >> strip_tac >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH fargs ==> ?entry. _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `supported_value_type tops (SND (EL i fargs))` by
    (fs[EVERY_EL, LENGTH_MAP] >> metis_tac[EL_MAP]) >>
  `MEM (FST (EL i fargs), SND (EL i fargs)) fargs` by
    (simp[MEM_EL, pairTheory.PAIR] >> qexists_tac `i` >> simp[]) >>
  drule_all ctor_formal_type_memory_bound >> strip_tac >>
  metis_tac[ctor_supported_value_strict_type_bounded, ctor_supported_value_inverse]
QED
