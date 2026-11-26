Theory s1PrefixSelectedDefaultGuards
Ancestors
  e2eDefs entryDispatchProps vyperTypeContractGetter vyperReadOnlySyntax
  s1PrefixCheckedDeclDefaults s1PrefixClassifiedDefaultGuard constSubst rich_list

Theorem selected_omitted_default_guards:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  EVERY (runtime_constant_expr [(NONE,tops)]) (DROP k dflts) /\
  no_sha256_exprs (DROP k dflts)
Proof
  strip_tac >>
  drule_all source_typing_ok_runtime_ready >> strip_tac >>
  drule lookup_function_External_cases >> strip_tac
  >- (drule_all checked_external_decl_default_facts >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      conj_tac >- (irule EVERY_DROP >> first_assum ACCEPT_TAC) >>
      Cases_on `tx.function_name = "__default__"`
      >- (qpat_x_assum `_ ==> dflts = []` mp_tac >>
          simp[no_sha256_collections]) >>
      drule_all lookup_function_external_member >>
      simp[subst_consts_fn_def] >> strip_tac >>
      drule_all lowered_classified_raw_defaults_no_sha >>
      simp[no_sha256_collections] >> metis_tac[EVERY_DROP]) >>
  drule external_getter_defaults >> simp[no_sha256_collections]
QED
