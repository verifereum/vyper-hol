(* Parameter capacities are checked before conversion to word literals. *)
Theory entryReachBodyRegistrationSizeBoundary
Ancestors
  entryReachBodyPackageAlignment externalEntryChecks compileVyper
  abiDecoderCoherence compileEnv list words arithmetic

Theorem entry_selected_allocs_ok:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?rr:bool. fn_allocs_ok tops (mut,F,rr,tx.function_name,args,[],ret,fbody)
Proof
  strip_tac >> drule_all selected_external_dispatch >> strip_tac >>
  Cases_on `classify_functions tops` >> rename1 `classify_functions tops = (exts,rest)` >>
  PairCases_on `rest` >> fs[] >>
  qexists_tac `rr` >> irule lower_vyper_runtime_unit_allocs_ok >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`rest2`, `exts`, `rest1`, `rest0`] >> simp[]
QED

Theorem entry_registration_parameter_capacity:
  fn_allocs_ok tops (mut,nr,(rr:bool),name,args,defaults,ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,raw,name,args,defaults,ret,fbody)) =
    (lbl,ce,pos,cds,pay,nr',key,ut,view,fbody',rt) /\
  compile_register_positional_args ce prefix off st = (next,last) /\
  i < LENGTH args ==>
  type_memory_bytes next (SND (EL i args)) < 2 ** 64
Proof
  strip_tac >> drule entry_runtime_package_layout >> strip_tac >>
  drule entry_registration_prefix_layout >> strip_tac >>
  `next.ce_struct_fields =
    (build_compile_env tops Internal mut name args ret fbody F).ce_struct_fields` by
    simp[build_compile_env_ce_struct_fields] >>
  `type_memory_bytes next (SND (EL i args)) =
    type_memory_bytes (build_compile_env tops Internal mut name args ret fbody F)
      (SND (EL i args))` by
    (irule type_memory_bytes_struct_fields >> simp[]) >>
  fs[fn_allocs_ok_def, EVERY_EL] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  Cases_on `EL i args` >> simp[]
QED

Theorem entry_selected_parameter_size_bound:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  supported_program tops /\ valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops T keys
      (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,cds,pay,F,key,ut,view,fbody,rt) /\
  compile_register_positional_args ce prefix off st = (next,last) /\
  i < LENGTH args /\
  abi_decoder_coherent next env next.ce_struct_fields (SND (EL i args)) tv ==>
  type_memory_size tv < dimword (:256)
Proof
  strip_tac >> drule_all entry_selected_allocs_ok >> strip_tac >>
  `type_memory_bytes next (SND (EL i args)) < 2 ** 64` by
    (irule entry_registration_parameter_capacity >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `2 ** 64 < dimword (:256)` by simp[dimword_def] >>
  metis_tac[LESS_TRANS]
QED
