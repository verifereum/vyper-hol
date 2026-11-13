Theory ctorSourceInputs
Ancestors
  valueEncodingDefs loweringStateRelDefs structFieldsProps entryStateRel entryArgPtrs abiCallerBuiltinInput abiDecoderCoherence
  compileVyper compileEnv vyperABIRoundtrip vyperInterpreter vyperTypeContract
  list finite_map

Theorem package_constructor_layout:
  package_constructor tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
    (ce_pack,pos_args,mut = Payable,nr,nkey_map fname,use_trans,fbody,ret) /\
  ce0 = (ce_pack with ce_imm_alloca := imm) ==>
  pos_args = build_positional_args ce0 fargs /\
  ce0.ce_struct_fields =
    (build_compile_env tops Deploy mut fname fargs ret fbody use_trans).ce_struct_fields /\
  ce0.ce_flag_n_members =
    (build_compile_env tops Deploy mut fname fargs ret fbody use_trans).ce_flag_n_members /\
  ce0.ce_vars =
    (build_compile_env tops Deploy mut fname fargs ret fbody use_trans).ce_vars
Proof
  simp[package_constructor_def, update_cenv_nonreentrant_def] >>
  rpt strip_tac >> gvs[build_positional_args_imm_alloca]
QED

Theorem package_constructor_memlocs:
  package_constructor tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
    (ce_pack,pos_args,mut = Payable,nr,nkey_map fname,use_trans,fbody,ret) /\
  ce0 = (ce_pack with ce_imm_alloca := imm) /\
  ALL_DISTINCT (MAP FST fargs) ==>
  EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs
Proof
  strip_tac >> drule_all package_constructor_layout >> strip_tac >>
  `ce0.ce_struct_fields = make_struct_fields_map tops` by
    simp[build_compile_env_ce_struct_fields] >>
  `ce0.ce_vars = FST (allocate_args
     (get_struct_fields (make_struct_fields_map tops)) fargs 0 FEMPTY)` by
    (simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  drule_then (qspecl_then [`get_struct_fields (make_struct_fields_map tops)`,
    `0`, `FEMPTY`] strip_assume_tac) allocate_args_lookup >>
  gvs[EVERY_MEM, GSYM type_mem_bytes_type_memory_bytes]
QED

Theorem package_constructor_coherent:
  package_constructor tops use_trans nkey_map
    (mut,nr,rr,fname,fargs,dflts,ret,fbody) =
    (ce_pack,pos_args,mut = Payable,nr,nkey_map fname,use_trans,fbody,ret) /\
  ce0 = (ce_pack with ce_imm_alloca := imm) /\
  contract_namespaces_ok T [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields ty tv
Proof
  strip_tac >> drule_all package_constructor_layout >> strip_tac >>
  irule abi_decoder_coherent_layout_transport >>
  qexists_tac `build_compile_env tops Deploy mut fname fargs ret fbody use_trans` >>
  simp[] >> irule abi_caller_coherent >> simp[] >> qexists_tac `T` >> simp[]
QED

(* Source binding and compiler packaging precede physical argument decoding.
   Strict ABI value validity is a separate interface: the checked source
   domain also admits fixed bytes of width zero. *)
Theorem constructor_bound_source_inputs:
  !tops use_trans nkey_map mut nr rr fname fargs dflts ret fbody
   ce_pack pos_args ce0 imm vals avs scope.
    package_constructor tops use_trans nkey_map
      (mut, nr, rr, fname, fargs, dflts, ret, fbody) =
      (ce_pack, pos_args, mut = Payable, nr, nkey_map fname, use_trans, fbody, ret) /\
    ce0 = (ce_pack with ce_imm_alloca := imm) /\
    contract_namespaces_ok T [((NONE:num option),tops)] /\
    EVERY (assignable_type (type_env tops)) (MAP SND fargs) /\
    ALL_DISTINCT (MAP FST fargs) /\
    bind_arguments (type_env tops) fargs vals = SOME scope /\
    vyper_to_abi_list (type_env tops) (MAP SND fargs) vals = SOME avs ==>
    pos_args = build_positional_args ce0 fargs /\
    LENGTH vals = LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
    EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
      SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
    (!i. i < LENGTH fargs ==>
      ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
        entry.value = EL i vals /\
        evaluate_type (type_env tops) (SND (EL i fargs)) = SOME entry.type /\
        value_has_type entry.type entry.value /\
        val_wf entry.type entry.value /\
        type_memory_size entry.type = type_memory_bytes ce0 (SND (EL i fargs)) /\
        abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields
          (SND (EL i fargs)) entry.type /\
        vyper_to_abi (type_env tops) (SND (EL i fargs)) entry.value = SOME (EL i avs)) /\
    (!func initial. local_ptrs_rel func ce0 [scope] initial)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all package_constructor_layout >> strip_tac >>
  drule_all package_constructor_memlocs >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >> fs[LENGTH_MAP] >>
  conj_tac
  >- (qx_gen_tac `i` >> strip_tac >>
      `i < LENGTH fargs` by simp[] >>
      drule_all bind_arguments_lookup_index >> strip_tac >>
      drule_all entryDecodePropsTheory.bind_arguments_word_arg >> strip_tac >>
      `assignable_type (type_env tops) (SND (EL i fargs))` by
        (qpat_x_assum `EVERY (assignable_type _) _` mp_tac >>
         pure_rewrite_tac[EVERY_EL, LENGTH_MAP] >>
         disch_then (qspec_then `i` mp_tac) >>
         simp[EL_MAP, NoAsms] >> metis_tac[]) >>
      `abi_decoder_coherent ce0 (type_env tops) ce0.ce_struct_fields
         (SND (EL i fargs)) tv` by
        (drule_all package_constructor_coherent >>
         disch_then assume_tac >> metis_tac[optionTheory.SOME_11]) >>
      drule abi_decoder_coherent_header >> strip_tac >>
      qexists_tac `<| assignable := T; type := tv; value := EL i vals; popped := [] |>` >>
      gvs[vyperStateTheory.lookup_scopes_def, abi_decoder_header_def] >>
      conj_tac >- (drule_all bind_arguments_memory_wf >> simp[]) >>
      qpat_x_assum `!i. _ ==> vyper_to_abi _ _ _ = _`
        (qspec_then `i` mp_tac) >> simp[EL_MAP]) >>
  rpt gen_tac >> drule_all bind_arguments_initial_local_ptrs >> simp[]
QED
