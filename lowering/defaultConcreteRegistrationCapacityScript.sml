(* Natural parameter capacities supplied by successful runtime lowering. *)
Theory defaultConcreteRegistrationCapacity
Ancestors defaultConcreteRegistrationDefs entryExternalPackageCoherence
  compileVyper moduleLowering compileEnv abiDecoderCoherence list rich_list words arithmetic

Theorem default_registration_capacity_from_lowering:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  classify_functions tops = (exts,ints,fb,ctor) /\
  (MEM (mut,nr,(rr:bool),fname,args,ds,ret,fbody) exts \/
   fb = SOME (mut,nr,rr,fname,args,ds,ret,fbody)) /\
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,raw,fname,args,ds,ret,fbody)) =
    (lbl,ce0,specs,mc,pay,nr',nk,ut,view,stmts,rt) /\
  default_registration_invariant tops cx ctx fn site k vs ce0 start
    args all_tvs specs cef sa ce0 start 4 specs all_tvs s G tn [] ==>
  EVERY (\tv. type_memory_size tv < dimword (:256)) all_tvs
Proof
  strip_tac >>
  `fn_allocs_ok tops (mut,nr,rr,fname,args,ds,ret,fbody)` by
    metis_tac[lower_vyper_runtime_unit_allocs_ok] >>
  drule external_package_layout >> strip_tac >>
  `ce0.ce_struct_fields =
    (build_compile_env tops Internal mut fname args ret fbody F).ce_struct_fields` by
    simp[build_compile_env_ce_struct_fields] >>
  `!ty. type_memory_bytes ce0 ty =
    type_memory_bytes (build_compile_env tops Internal mut fname args ret fbody F) ty` by
    (gen_tac >> irule type_memory_bytes_struct_fields >> simp[]) >>
  `!i. i < LENGTH args ==>
    type_memory_bytes ce0 (SND (EL i args)) < 2 ** 64` by
    (fs[fn_allocs_ok_def, EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
     Cases_on `EL i args` >> simp[]) >>
  fs[default_registration_invariant_def] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `n < LENGTH args` by metis_tac[] >>
  `default_registration_slot tops ce0
    (EL n (ZIP (args,all_tvs))) (EL n specs)` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `EL n (ZIP (args,all_tvs)) = (EL n args, EL n all_tvs)` by
    metis_tac[EL_ZIP] >>
  `type_memory_size (EL n all_tvs) = type_memory_bytes ce0 (SND (EL n args))` by
    (Cases_on `EL n args` >>
     qmatch_asmsub_abbrev_tac `default_registration_slot tops ce0 pair spec` >> PairCases_on `spec` >>
     fs[Abbr `pair`, EL_ZIP, default_registration_slot_def] >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  `2 ** 64 < dimword (:256)` by simp[dimword_def] >>
  qpat_x_assum `!i. i < LENGTH args ==> _` (qspec_then `n` mp_tac) >>
  simp[dimword_def]
QED
