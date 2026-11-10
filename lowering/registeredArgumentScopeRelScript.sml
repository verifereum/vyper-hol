(* Scope correspondence from the indexed registration certificate. *)
Theory registeredArgumentScopeRel
Ancestors
  loweringStateRelDefs entryReachBodyRegistrationSlotWitness calldataRegistrationLocals
  externalBodyFrame entryLocals entryStateRel intCallCallee
  compileVyper compileEnv venomState list

Theorem registered_arguments_local_ptrs:
  bind_arguments tenv args values = SOME env /\
  ALL_DISTINCT (MAP FST args) /\
  entry_prefix_witness fn tenv args values (LENGTH args) cef registered t /\
  alloca_inv t /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved cef st ==>
  local_ptrs_rel fn cef [env] t
Proof
  strip_tac >> irule decoded_scope_local_ptrs >>
  reverse conj_tac >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all decoded_arguments_scope_lookup >> strip_tac >>
  fs[entry_prefix_witness_def] >>
  first_x_assum drule >>
  simp[entry_slot_witness_def] >> strip_tac >>
  gvs[eval_operand_def] >>
  qexistsl_tac [`p`, `ins`] >> simp[] >>
  irule memoryValueEncodingTheory.val_in_memory_memory_value_rel >> simp[] >>
  drule_then (qspec_then `i` mp_tac) entryDecodePropsTheory.bind_arguments_word_arg >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem external_target_registered_reserved:
  set_external_package_target target
    (package_external_fn tops use_trans nkeys
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pos,rest) /\
  ALL_DISTINCT (MAP FST args) /\
  compile_register_positional_args ce pos 4 start = (cef,registered) ==>
  local_ptrs_reserved cef registered
Proof
  strip_tac >>
  Cases_on `package_external_fn tops use_trans nkeys
    (mut,nr,rr,name,args,dflts,ret,fbody)` >>
  PairCases_on `r` >> gvs[set_external_package_target_def] >>
  drule_all package_external_fn_vars >> strip_tac >>
  `r0.ce_imm_alloca = NONE` by
    (gvs[package_external_fn_def, update_cenv_nonreentrant_def] >>
     rw[update_cenv_ret_abi_def, build_compile_env_imm_alloca]) >>
  `MAP FST pos = MAP FST args` by
    (qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def] >> strip_tac >>
     gvs[build_positional_args_names]) >>
  drule compile_register_positional_args_reserved >>
  impl_tac >-
    (simp[] >> gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
     metis_tac[optionTheory.SOME_11, optionTheory.NOT_SOME_NONE,
       compileEnvTheory.var_location_distinct]) >> simp[]
QED
