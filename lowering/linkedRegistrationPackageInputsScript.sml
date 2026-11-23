(* A linked external package's ABI head size and its allocated arguments. *)
Theory linkedRegistrationPackageInputs
Ancestors
  linkedAbiDecodeMetadata linkedStructMemorySize exprSimAbiDecodeEntryCoherence
  entryStateRel calldataSourceSize structFieldsProps compileUnit compileVyper
  compileEnv loweringStateRelDefs vyperTypeContract vyperTypeSystem
  vyperTypeArgFits vyperValue vyperMisc moduleLowering vfmConstants finite_map list pair words

Theorem linked_registration_package_inputs:
  contract_namespaces_ok F mods /\
  params_ok (type_env_all_modules mods) args /\
  fn_allocs_ok_unit mods (src,(mut,nr,rr,name,args,dflts,ret,body_code)) /\
  set_external_package_target rp.rpol_target
    (package_external_fn_unit mods T (K global_nonreentrant_slot)
      (src,(mut,nr,rr,name,args,([]:expr list),ret,body_code))) =
    (lbl,ce,pos,mincd,pay,nr,key,tr,view,body_code,rt) ==>
  lbl = "fn_" ++ name /\ ALL_DISTINCT (MAP FST args) /\
  pos = build_positional_args ce args /\
  ?tvs. OPT_MMAP (evaluate_type (type_env_all_modules mods)) (MAP SND args) =
          SOME tvs /\
    mincd = 4 + SUM (MAP tv_abi_size tvs) /\ mincd < dimword (:256) /\
    LIST_REL (\(argname,ty) (ty',tv). ty = ty' /\
      abi_decoder_coherent ce (type_env_all_modules mods) ce.ce_struct_fields ty tv /\
      (?loc. FLOOKUP ce.ce_vars argname = SOME loc /\
        var_location_memory_size loc = SOME (type_memory_size tv)) /\
      type_memory_size tv < dimword (:256)) args (ZIP (MAP SND args,tvs))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `sf = make_struct_fields_map_mods mods` >>
  qabbrev_tac `tenv = type_env_all_modules mods` >>
  `lbl = "fn_" ++ name /\ ce.ce_struct_fields = sf /\
   ce.ce_flag_n_members = SND (build_flag_info_mods mods (K (K 0)) (K 0)) /\
   ce.ce_vars = FST (allocate_args (get_struct_fields sf) args 0 FEMPTY) /\
   pos = build_positional_args ce args /\
   mincd = 4 + SUM (MAP (abi_embedded_static_size sf) (MAP SND args))` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     Cases_on `ret = NoneT` >>
     simp[package_external_fn_unit_def, set_external_package_target_def,
          update_cenv_nonreentrant_def, update_cenv_ret_abi_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_x_assum `_ = ce` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `_ = pos` (SUBST1_TAC o SYM) >>
     qpat_x_assum `_ = mincd` (SUBST1_TAC o SYM) >>
     simp[min_calldata_size_def, MAP_MAP_o, combinTheory.o_DEF,
          pairTheory.LAMBDA_PROD] >>
     rpt conj_tac >> TRY (irule build_positional_args_layout_cong) >>
     simp[build_compile_env_unit_def, pairTheory.ELIM_UNCURRY, Abbr `sf`]) >>
  qpat_assum `params_ok tenv args`
    (strip_assume_tac o REWRITE_RULE [params_ok_def]) >>
  `?tvs. LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP SND args) tvs` by
    (irule well_formed_types_evaluate >>
     fs[EVERY_MAP, EVERY_MEM, FORALL_PROD, combinTheory.o_DEF] >>
     metis_tac[assignable_type_well_formed]) >>
  `OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs` by
    (simp[OPT_MMAP_SOME_IFF, EVERY_MAP, EVERY_EL, LIST_EQ_REWRITE] >>
     fs[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     first_x_assum (drule_then assume_tac) >> gvs[]) >>
  `abi_decode_root_metadata ce tenv` by
    (simp[Abbr `tenv`] >> irule linked_abi_decode_root_metadata >>
     fs[Abbr `sf`] >> qexists_tac `F` >> simp[]) >>
  `LIST_REL (\(nm,ty) tv. abi_decoder_coherent ce tenv sf ty tv) args tvs` by
    (fs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rpt strip_tac >>
     Cases_on `EL n args` >> simp[] >>
     qpat_assum `ce.ce_struct_fields = sf` (SUBST1_TAC o SYM) >>
     irule abi_decode_root_coherent >> asm_rewrite_tac[] >>
     qpat_assum `!i. i < LENGTH args ==> evaluate_type _ _ = _`
       (qspec_then `n` mp_tac) >>
     qpat_assum `!i. i < LENGTH tvs ==> (\(_,ty). assignable_type tenv ty) _`
       (qspec_then `n` mp_tac) >>
     qpat_assum `EL n args = _` (fn arg =>
       qpat_assum `LENGTH args = LENGTH tvs` (fn len =>
         qpat_assum `n < LENGTH tvs` (fn bound =>
           simp_tac (srw_ss()) [arg,len,bound])))) >>
  `MAP (abi_embedded_static_size sf) (MAP SND args) = MAP tv_abi_size tvs` by
    (simp[LIST_EQ_REWRITE] >>
     fs[LIST_REL_EL_EQN] >> rpt strip_tac >> simp[EL_MAP] >>
     Cases_on `EL x args` >> simp[] >>
     `abi_decoder_coherent ce tenv sf r (EL x tvs)` by
       (qpat_assum `!n. n < LENGTH args ==> (\(nm,ty) tv. _) _ _`
          (qspec_then `x` mp_tac) >>
        qpat_assum `EL x args = _` (fn arg =>
          qpat_assum `LENGTH args = LENGTH tvs` (fn len =>
            qpat_assum `x < LENGTH tvs` (fn bound =>
              simp_tac (srw_ss()) [arg,len,bound])))) >>
     qpat_assum `ce.ce_struct_fields = sf` (SUBST1_TAC o SYM) >>
     drule_then ACCEPT_TAC calldata_coherent_embedded_size) >>
  `EVERY (\(_,ty). type_mem_bytes (get_struct_fields sf) ty < 2 ** 64) args /\
   abi_size_bound sf (TupleT (MAP SND args)) < 2 ** 128` by
    fs[fn_allocs_ok_unit_def, GSYM type_mem_bytes_type_memory_bytes,
       build_compile_env_unit_def, pairTheory.ELIM_UNCURRY, Abbr `sf`] >>
  `!ts. SUM (MAP (abi_embedded_static_size sf) ts) <= abi_size_bound sf (TupleT ts)` by
    (Induct >- simp[abi_size_bound_def] >>
     qpat_assum `SUM _ <= abi_size_bound _ (TupleT _)`
       (mp_tac o ONCE_REWRITE_RULE [abi_size_bound_def]) >>
     simp_tac (srw_ss()) [Once abi_size_bound_def] >>
     decide_tac) >>
  `mincd < dimword (:256)` by
    (qpat_assum `MAP (abi_embedded_static_size sf) _ = _` (fn sizes =>
       qpat_assum `!ts. SUM _ <= _`
         (qspec_then `MAP SND args` (assume_tac o REWRITE_RULE [sizes]))) >>
     fs[dimword_def] >> decide_tac) >>
  asm_rewrite_tac[] >> qexists_tac `tvs` >> asm_rewrite_tac[] >>
  drule_then (qspecl_then [`get_struct_fields sf`, `0`, `FEMPTY`] strip_assume_tac)
    allocate_args_lookup >>
  fs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rpt strip_tac >>
  simp[EL_ZIP, EL_MAP] >>
  Cases_on `EL n args` >> rename1 `EL n args = (argname,ty)` >> simp[] >>
  `evaluate_type tenv ty = SOME (EL n tvs)` by
    (qpat_assum `!i. i < LENGTH tvs ==> evaluate_type _ _ = _`
       (qspec_then `n` mp_tac) >>
     qpat_assum `EL n args = _` (fn arg =>
       qpat_assum `n < LENGTH tvs` (fn bound =>
         simp_tac (srw_ss()) [arg,bound]))) >>
  `type_mem_bytes (get_struct_fields sf) ty = type_memory_size (EL n tvs)` by
    (qpat_assum `ce.ce_struct_fields = sf` (SUBST1_TAC o SYM) >>
     rewrite_tac[type_mem_bytes_type_memory_bytes] >>
     mp_tac (Q.INST [`dep` |-> `F`,`env` |-> `tenv`,`tv` |-> `EL n tvs`]
       (SPEC_ALL make_struct_fields_map_mods_memory_size)) >>
     simp[Abbr `sf`, Abbr `tenv`]) >>
  gvs[var_location_memory_size_def, dimword_def] >>
  conj_tac
  >- (qpat_assum `!i. i < LENGTH tvs ==> (\(nm,ty) tv. abi_decoder_coherent _ _ _ ty tv) _ _`
        (qspec_then `n` mp_tac) >>
      qpat_assum `EL n args = _` (fn arg =>
        qpat_assum `n < LENGTH tvs` (fn bound =>
          simp_tac (srw_ss()) [arg,bound]))) >>
  conj_tac
  >- (qpat_assum `!i. i < LENGTH tvs ==> ?p. FLOOKUP _ _ = _`
        (qspec_then `n` mp_tac) >>
      qpat_assum `EL n args = _` (fn arg =>
        qpat_assum `n < LENGTH tvs` (fn bound =>
          qpat_assum `type_mem_bytes _ ty = _` (fn size =>
            simp_tac (srw_ss()) [arg,bound,size]))) >>
      disch_then (qx_choose_then `p` assume_tac) >>
      qexists_tac `MemLoc p (type_memory_size (EL n tvs))` >>
      simp[var_location_memory_size_def]) >>
  qpat_assum `!i. i < LENGTH tvs ==> (\(_,ty). type_mem_bytes _ ty < _) _`
    (qspec_then `n` mp_tac) >>
  qpat_assum `EL n args = _` (fn arg =>
    qpat_assum `n < LENGTH tvs` (fn bound =>
      qpat_assum `type_mem_bytes _ ty = _` (fn size =>
        simp_tac (srw_ss()) [arg,bound,size]))) >>
  decide_tac
QED
