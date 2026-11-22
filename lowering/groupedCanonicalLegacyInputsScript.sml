(* Typed canonical arguments and the installed minimum for a legacy job. *)
Theory groupedCanonicalLegacyInputs
Ancestors
  registrationRejectMetadata entryChecksProps entryDecodePlanProps
  entryDecodeProps entryStateRel externalReturnPackage vyperTypeABI
  e2eDefs compileVyper vyperInterpreter constSubst list option

Theorem grouped_canonical_legacy_inputs:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  valid_vyper_call tops tx cd ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) /\
  MEM (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)
    (FST (classify_functions tops)) /\
  set_external_package_target policy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,[],ret,subst_consts_stmts (module_consts_env tops []) fbody)) =
    (lbl,ce0,pa,m,pay,nr',key,ut,view,ss,rt) ==>
  ?envb tvs.
    bind_arguments (type_env tops) args tx.args = SOME envb /\
    OPT_MMAP (evaluate_type (type_env tops)) (MAP SND args) = SOME tvs /\
    LIST_REL value_has_type tvs tx.args /\ LENGTH tx.args = LENGTH args /\
    calldata_encodes (type_env tops) tx.function_name (MAP SND args) tx.args cd /\
    m = 4 + SUM (MAP tv_abi_size tvs) /\ m <= LENGTH cd
Proof
  strip_tac >>
  qpat_x_assum `valid_vyper_call _ _ _ _` mp_tac >>
  simp[valid_vyper_call_def, IS_SOME_EXISTS] >> strip_tac >>
  drule return_package_target_inversion >>
  disch_then (qx_choose_then `ce` strip_assume_tac) >>
  `m <= LENGTH cd` by
    (`ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
       metis_tac[source_typing_ok_type_def_keys_distinct] >>
     drule_all package_external_fn_dec_cenv_agrees >> strip_tac >>
     `m = min_calldata_size ce args 0` by
       (qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
        simp[package_external_fn_def] >> rw[] >> simp[]) >>
     simp[] >> irule calldata_encodes_min_calldata_size >>
     qexistsl_tac [`tx.function_name`,`type_env tops`,`tx.args`] >>
     simp[] >> rpt strip_tac >> drule_all bind_arguments_word_arg >> simp[]) >>
  drule_all registration_reject_classified_package_inputs >> strip_tac >>
  rename1 `OPT_MMAP _ _ = SOME tvs` >>
  rename1 `bind_arguments _ _ _ = SOME envb` >>
  qexistsl_tac [`envb`,`tvs`] >> simp[] >>
  drule_then assume_tac OPT_MMAP_LIST_REL >>
  drule_then assume_tac OPT_MMAP_LENGTH >>
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  qpat_assum `LIST_REL _ (MAP SND args) tvs`
    (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  simp[EL_MAP] >> disch_then drule >> strip_tac >>
  drule_all bind_arguments_word_arg >> simp[]
QED
