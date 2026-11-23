(* Derive constructor ABI metadata from the actual linked package. *)
Theory linkedConstructorRegistrationMetadata
Ancestors
  linkedAbiDecodeMetadata linkedStructMemorySize exprSimAbiDecodeEntryCoherence
  ctorDeployMemoryRunMemEntryAggregate abiDecoderCoherence abiDecoderMembers
  entryStateRel entryArgPtrs entryDecodeProps structFieldsProps compileUnit valueTypingMemoryProps
  compileVyper compileEnv loweringStateRelDefs vyperTypeContract
  vyperABIRoundtrip vyperABI contractABI vyperValue vyperState words finite_map list pair

Theorem linked_constructor_registration_metadata:
  params_ok (type_env_all_modules mods) formals /\
  contract_namespaces_ok T mods /\
  fn_allocs_ok_unit mods (NONE,(mut,F,F,"__init__",formals,[],NoneT,body_code)) /\
  set_constructor_package_target target
    (package_constructor_unit mods T (K global_nonreentrant_slot)
      (mut,F,F,"__init__",formals,[],NoneT,body_code)) =
    (ce_pack,pos,mut = Payable,F,global_nonreentrant_slot,T,body_code,NoneT) /\
  ce = ce_pack with ce_imm_alloca := imm /\
  bind_arguments (type_env_all_modules mods) formals vals = SOME scope /\
  vyper_to_abi_list (type_env_all_modules mods) (MAP SND formals) vals = SOME avs ==>
  pos = build_positional_args ce formals /\
  LENGTH avs = LENGTH formals /\ ALL_DISTINCT (MAP FST formals) /\
  has_types (vyper_to_abi_types (type_env_all_modules mods) (MAP SND formals)) avs /\
  EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) formals /\
  EVERY (\a. type_memory_bytes ce (SND a) < dimword (:256)) formals /\
  (!func initial. local_ptrs_rel func ce [scope] initial) /\
  (!i. i < LENGTH formals ==>
    ?entry. lookup_scopes (FST (EL i formals)) [scope] = SOME entry /\
      val_wf entry.type entry.value /\
      type_memory_size entry.type <= type_memory_bytes ce (SND (EL i formals)) /\
      abi_decoder_coherent ce (type_env_all_modules mods) ce.ce_struct_fields
        (SND (EL i formals)) entry.type /\
      abi_decoder_metadata ce (type_env_all_modules mods) (SND (EL i formals)) entry.type
        (type_to_abi_dec_info ce.ce_struct_fields ce (SND (EL i formals)))
        (EL i avs) entry.value)
Proof
  strip_tac >>
  qabbrev_tac `tenv = type_env_all_modules mods` >>
  qabbrev_tac `sf = make_struct_fields_map_mods mods` >>
  `pos = build_positional_args ce formals /\ ce.ce_struct_fields = sf /\
   ce.ce_flag_n_members = SND (build_flag_info_mods mods (K (K 0)) (K 0)) /\
   ce.ce_vars = FST (allocate_args (get_struct_fields sf) formals 0 FEMPTY)` by
    (qpat_assum `set_constructor_package_target _ _ = _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [set_constructor_package_target_def, update_cenv_nonreentrant_def] o
        SIMP_RULE (srw_ss()) [package_constructor_unit_def, LET_THM]) >>
     qpat_assum `ce = _` SUBST1_TAC >>
     qpat_assum `_ = ce_pack` (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [build_positional_args_imm_alloca] >>
     conj_tac
     >- (qpat_assum `build_positional_args _ formals = pos` (SUBST1_TAC o SYM) >>
         irule build_positional_args_layout_cong >> simp[]) >>
     simp[build_compile_env_unit_def, pairTheory.ELIM_UNCURRY, Abbr `sf`]) >>
  qpat_assum `params_ok tenv formals`
    (strip_assume_tac o REWRITE_RULE [params_ok_def]) >>
  `EVERY (\a. ?off. FLOOKUP ce.ce_vars (FST a) =
    SOME (MemLoc off (type_memory_bytes ce (SND a)))) formals` by
    (drule_then (qspecl_then [`get_struct_fields sf`,`0`,`FEMPTY`] strip_assume_tac)
       allocate_args_lookup >>
     fs[GSYM type_mem_bytes_type_memory_bytes]) >>
  `EVERY (\a. type_memory_bytes ce (SND a) < dimword (:256)) formals` by
    (`EVERY (\(_,ty). type_mem_bytes (get_struct_fields sf) ty < 2 ** 64) formals` by
       fs[fn_allocs_ok_unit_def, LET_THM, GSYM type_mem_bytes_type_memory_bytes,
          build_compile_env_unit_def, pairTheory.ELIM_UNCURRY, Abbr `sf`] >>
     simp_tac bool_ss [EVERY_MEM] >> qx_gen_tac `arg` >> strip_tac >>
     qpat_assum `EVERY (\(_,ty). type_mem_bytes _ ty < 2 ** 64) formals`
       (qspec_then `arg` mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `arg` >> simp[GSYM type_mem_bytes_type_memory_bytes, dimword_def] >>
     decide_tac) >>
  `!func initial. local_ptrs_rel func ce [scope] initial` by
    (rpt gen_tac >> irule bind_arguments_initial_local_ptrs >> metis_tac[]) >>
  `abi_decode_root_metadata ce tenv` by
    (simp_tac (srw_ss()) [Abbr `tenv`] >>
     irule (Q.INST [`dep` |-> `T`] linked_abi_decode_root_metadata) >>
     simp_tac (srw_ss()) [GSYM (Abbr `sf`)] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule vyper_to_abi_list_EL >> strip_tac >> fs[LENGTH_MAP] >>
  `!i. i < LENGTH formals ==>
    ?entry. lookup_scopes (FST (EL i formals)) [scope] = SOME entry /\
      val_wf entry.type entry.value /\
      type_memory_size entry.type <= type_memory_bytes ce (SND (EL i formals)) /\
      abi_decoder_coherent ce tenv ce.ce_struct_fields (SND (EL i formals)) entry.type /\
      has_type (vyper_to_abi_type tenv (SND (EL i formals))) (EL i avs) /\
      abi_decoder_metadata ce tenv (SND (EL i formals)) entry.type
        (type_to_abi_dec_info ce.ce_struct_fields ce (SND (EL i formals)))
        (EL i avs) entry.value` by
    (gen_tac >> strip_tac >>
     drule_all bind_arguments_lookup_index >>
     disch_then (qx_choose_then `tv` strip_assume_tac) >>
     drule_all bind_arguments_word_arg >> strip_tac >>
     `tv' = tv` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `tv' = tv` SUBST_ALL_TAC >>
     `val_wf tv (EL i vals)` by
       (drule_then ACCEPT_TAC value_has_type_memory_wf) >>
     `assignable_type tenv (SND (EL i formals))` by
       (qpat_assum `EVERY (\(_,ty). assignable_type _ ty) formals`
          (qspec_then `i` mp_tac o PURE_REWRITE_RULE [EVERY_EL]) >>
        Cases_on `EL i formals` >> simp[]) >>
     `type_memory_bytes ce (SND (EL i formals)) = type_memory_size tv` by
       (irule (Q.INST [`dep` |-> `T`, `env` |-> `type_env_all_modules mods`]
          (SPEC_ALL make_struct_fields_map_mods_memory_size)) >>
        fs[Abbr `sf`, Abbr `tenv`] >> qexists_tac `mods` >> fs[]) >>
     `type_memory_size tv < dimword (:256)` by
       (qpat_assum `EVERY (\a. type_memory_bytes ce (SND a) < _) formals`
          (qspec_then `i` mp_tac o SIMP_RULE bool_ss [EVERY_EL]) >>
        simp[]) >>
     `i < LENGTH vals` by
       (qpat_assum `LENGTH vals = LENGTH formals` SUBST1_TAC >>
        first_assum ACCEPT_TAC) >>
     `vyper_to_abi tenv (SND (EL i formals)) (EL i vals) = SOME (EL i avs)` by
       (qpat_assum `!j. j < LENGTH vals ==> vyper_to_abi _ _ _ = _`
          (qspec_then `i` mp_tac) >>
        qpat_assum `i < LENGTH vals` (fn vals_bound =>
          qpat_assum `i < LENGTH formals` (fn formals_bound =>
            simp[NoAsms, EL_MAP, vals_bound, formals_bound]))) >>
     `has_type (vyper_to_abi_type tenv (SND (EL i formals))) (EL i avs)` by
       (drule_all (cj 1 ctor_evaluated_abi_valid) >> simp[]) >>
     `abi_to_vyper tenv (SND (EL i formals)) (EL i avs) = SOME (EL i vals)` by
       (drule_all (cj 1 ctor_evaluated_abi_inverse) >> simp[]) >>
     `abi_decoder_coherent ce tenv ce.ce_struct_fields (SND (EL i formals)) tv` by
       (irule abi_decode_root_coherent >> asm_rewrite_tac[]) >>
     `abi_decoder_metadata ce tenv (SND (EL i formals)) tv
       (type_to_abi_dec_info ce.ce_struct_fields ce (SND (EL i formals)))
       (EL i avs) (EL i vals)` by
       (irule (Q.INST [`sf` |-> `ce.ce_struct_fields`]
          abi_decoder_coherent_root_metadata) >> asm_rewrite_tac[]) >>
     qexists_tac `<|assignable := T; type := tv; value := EL i vals; popped := []|>` >>
     qpat_assum `FLOOKUP scope (FST (EL i formals)) = _` (fn binding =>
       qpat_assum `val_wf tv (EL i vals)` (fn well_formed =>
         qpat_assum `type_memory_bytes ce (SND (EL i formals)) = _` (fn size =>
           qpat_assum `abi_decoder_coherent ce tenv ce.ce_struct_fields _ tv` (fn coherent =>
             qpat_assum `abi_decoder_metadata ce tenv _ tv _ _ _` (fn metadata =>
               simp[NoAsms, lookup_scopes_def, binding, well_formed, size,
                    coherent, metadata]))))) >>
     first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> conj_tac
  >- (simp[has_types_LIST_REL, vyper_to_abi_types_MAP, LIST_REL_EL_EQN, EL_MAP] >>
      gen_tac >> disch_tac >> first_x_assum drule >> metis_tac[]) >>
  gen_tac >> disch_tac >> first_x_assum drule >> metis_tac[]
QED
