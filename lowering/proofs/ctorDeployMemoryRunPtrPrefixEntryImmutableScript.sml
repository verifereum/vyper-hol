(* Zero immutable initialization, isolated from optimizer execution. *)
Theory ctorDeployMemoryRunPtrPrefixEntryImmutable
Ancestors
  ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs
  ctorDeployLoweringEntryTransport ctorDeployLoweringEntrySourceFrame
  compileVyper vyperInterpreter moduleLowering
  immutableEncoding immutableEncodingProofs immutableSectionRel immutableValue
  immutableRelation valueEncoding valueEncodingProps valueEncodingProofs
  vyperValue vyperTypeInitialState vyperTypeContractStaticMaps
  vyperTypeConstantCells abiCallerBuiltinInput entryStateRel
  rich_list list finite_map compileEnv loweringSlice

Theorem prefix_entry_zero_word_bytes[local]:
  word_to_bytes (0w:bytes32) T = REPLICATE 32 (0w:word8)
Proof
  simp[byteTheory.word_to_bytes_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC >>
  simp[wordsTheory.ZERO_SHIFT, wordsTheory.w2w_0]
QED

Theorem prefix_entry_zero_address_bytes[local]:
  word_to_bytes (0w:160 word) T = REPLICATE 20 (0w:word8)
Proof
  simp[byteTheory.word_to_bytes_def,
       fcpLib.INDEX_CONV ``dimindex(:160)``] >> EVAL_TAC >>
  simp[wordsTheory.ZERO_SHIFT, wordsTheory.w2w_0]
QED

Theorem prefix_entry_fit_zero[local]:
  immutable_fit n (REPLICATE m (0w:word8)) = REPLICATE n 0w
Proof
  simp[immutable_fit_def, REPLICATE_APPEND, REPLICATE_GENLIST,
       TAKE_GENLIST, arithmeticTheory.MIN_DEF]
QED

Theorem prefix_entry_flat_zero_slots[local]:
  !n sz. FLAT (GENLIST (\i. REPLICATE sz (0w:word8)) n) =
    REPLICATE (n * sz) 0w
Proof
  Induct >> simp[GENLIST_CONS, combinTheory.o_DEF,
    REPLICATE_APPEND, arithmeticTheory.MULT]
QED

Theorem prefix_entry_padded_zero_word[local]:
  (word_of_bytes_be (PAD_RIGHT 0w 32 (REPLICATE n 0w)):bytes32) = 0w /\
  (word_of_bytes_be (PAD_LEFT 0w 32 (REPLICATE n 0w)):bytes32) = 0w
Proof
  simp[PAD_RIGHT, PAD_LEFT, GSYM REPLICATE_GENLIST,
       REPLICATE_APPEND, byteTheory.word_of_bytes_be_def,
       immutable_word_of_zero_bytes]
QED

Theorem prefix_entry_default_encoding[local]:
  (!tv. encode_immutable_value tv (default_value tv) =
    REPLICATE (type_memory_size tv) 0w) /\
  (!tvs. encode_immutable_tuple tvs (MAP default_value tvs) =
    REPLICATE (type_memory_size_list tvs) 0w) /\
  (!fts. encode_immutable_fields fts
    (MAP (\(id,t). (id, default_value t)) fts) =
    REPLICATE (type_memory_size_fields fts) 0w)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  rw[default_value_def, default_value_tuple_MAP, default_value_struct_MAP,
     encode_immutable_value_def, type_memory_size_def,
     immutable_word_bytes_def, typed_val_to_w256_def, val_to_w256_def,
     integer_wordTheory.i2w_0, prefix_entry_padded_zero_word,
     prefix_entry_zero_word_bytes, prefix_entry_zero_address_bytes,
     prefix_entry_flat_zero_slots, prefix_entry_fit_zero, REPLICATE_APPEND]
QED

Theorem prefix_entry_zero_section[local]:
  (!pre vis name ty slot post.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post ==>
    ?tv. FLOOKUP (get_source_immutables NONE imms) name =
      SOME (tv, default_value tv) /\
      immutable_value_admissible tv (default_value tv) /\
      type_memory_size tv =
        type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty) ==>
  immutables_section_rel tops imms (REPLICATE (imm_len tops) 0w)
Proof
  strip_tac >> rewrite_tac[immutables_section_rel_def] >>
  conj_tac >- simp[imm_len_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `imm_len tops =
     compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre +
     type_memory_size tv +
     compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) post` by
    simp[imm_len_def, compute_immutables_len_append, compute_immutables_len_def] >>
  qpat_x_assum `tops = _` kall_tac >>
  qexistsl [`tv`, `default_value tv`] >> asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `compute_immutables_len sf pre` >>
  qmatch_goalsub_abbrev_tac `compute_immutables_len sf post` >>
  qpat_x_assum `type_memory_size tv = _`
    (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[GSYM REPLICATE_APPEND, APPEND_ASSOC] >>
  conj_tac
  >- (qspec_then `tv` mp_tac (cj 1 immutable_default_zero_decodes_mutual) >>
      disch_then (qspecl_then
        [`REPLICATE (compute_immutables_len sf pre) 0w`,
         `REPLICATE (compute_immutables_len sf post) 0w`] mp_tac) >> simp[]) >>
  simp[mem_bytes_at_def, DROP_APPEND, TAKE_APPEND, GSYM prefix_entry_default_encoding] >>
  `type_memory_size tv -
     (type_memory_size tv + compute_immutables_len sf post) = 0` by decide_tac >>
  simp[TAKE_LENGTH_TOO_LONG, encode_immutable_value_length, immutable_value_bytes_encoded]
QED

Theorem prefix_entry_initial_module_defaults[local]:
  !env src ts acc imms.
    initial_immutables_module env src ts acc = SOME imms ==>
    ((!id tv v. FLOOKUP (get_source_immutables src acc) id = SOME (tv,v) ==>
                  v = default_value tv) ==>
     (!id tv v. FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
                  v = default_value tv))
Proof
  recInduct initial_immutables_module_ind >>
  simp[initial_immutables_module_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  gen_tac >> strip_tac >>
  first_x_assum drule >> disch_then drule >>
  disch_then assume_tac >> strip_tac >>
  `!key ty value.
     FLOOKUP (get_source_immutables src_id_opt
       (update_immutable src_id_opt id tv (default_value tv) acc)) key =
       SOME (ty,value) ==> value = default_value ty`
    suffices_by metis_tac[] >>
  rpt gen_tac >>
  simp[vyperStateTheory.update_immutable_def,
       get_source_immutables_set_same, FLOOKUP_UPDATE] >>
  Cases_on `key = id` >> simp[] >> metis_tac[]
QED

Theorem prefix_entry_initial_defaults[local]:
  initial_immutables env [(NONE,tops)] = SOME imms /\
  FLOOKUP (get_source_immutables NONE imms) id = SOME (tv,v) ==>
  v = default_value tv
Proof
  simp[initial_immutables_def] >> strip_tac >>
  drule prefix_entry_initial_module_defaults >>
  gvs[vyperStateTheory.empty_immutables_def,
      vyperStateTheory.get_source_immutables_def] >> metis_tac[]
QED

Theorem prefix_entry_checked_decl[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  assignable_type (type_env tops) ty /\ contract_namespaces_ok T [(NONE,tops)]
Proof
  strip_tac >>
  `check_toplevel_decl [(NONE,tops)] art NONE
     (VariableDecl vis Immutable name ty slot)` by
    (irule check_contract_toplevel_decl_MEM_checked >> simp[] >> metis_tac[]) >>
  gvs[vyperTypeContractTheory.check_toplevel_decl_def, deploy_ctor_singleton_type_env] >>
  metis_tac[check_contract_artifact_fields]
QED

Theorem prefix_entry_checked_bare_lookup[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  FLOOKUP art.cta_bare_globals (NONE,name) = SOME ty
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  gvs[build_contract_type_artifact_nonsig_mode_irrelevant] >>
  irule build_contract_type_artifact_bare_globals_complete >>
  simp[] >> metis_tac[contract_namespaces_ok_deploy_implies_runtime]
QED

Theorem prefix_entry_checked_immutable_types[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  !vis' ty' slot'. MEM (VariableDecl vis' Immutable name ty' slot') tops ==> ty' = ty
Proof
  strip_tac >> drule_all prefix_entry_checked_bare_lookup >> strip_tac >>
  qpat_x_assum `MEM (VariableDecl vis Immutable name ty slot) tops` kall_tac >>
  rpt strip_tac >> drule_all prefix_entry_checked_bare_lookup >> simp[]
QED

Theorem prefix_entry_checked_decl_keys[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  strip_tac >> drule check_contract_artifact_fields >> strip_tac >>
  irule contract_namespaces_ok_module_toplevel_vtype_keys >>
  qexists `[(NONE,tops)]` >> simp[] >>
  metis_tac[contract_namespaces_ok_deploy_implies_runtime]
QED

Theorem prefix_entry_checked_initial_lookup[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms ==>
  ?tv v. FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) /\
         evaluate_type (type_env tops) ty = SOME tv
Proof
  strip_tac >>
  `is_immutable_decl name tops` by metis_tac[is_immutable_decl_MEM] >>
  `find_var_decl_by_name name tops = NONE` by
    (irule find_var_decl_by_name_NONE_Immutable >>
     metis_tac[prefix_entry_checked_decl_keys]) >>
  `IS_SOME (FLOOKUP (get_source_immutables NONE imms) name)` by
    (irule initial_immutables_contains_decl >>
     qexistsl [`[(NONE,tops)]`, `type_env_all_modules [(NONE,tops)]`, `tops`] >> simp[]) >>
  Cases_on `FLOOKUP (get_source_immutables NONE imms) name` >> gvs[] >>
  PairCases_on `x` >> simp[] >>
  irule initial_immutables_all_bare_global_type >>
  qexistsl [`name`, `imms`, `[(NONE,tops)]`, `NONE`, `tops`, `x1`] >>
  gvs[deploy_ctor_singleton_type_env] >>
  metis_tac[prefix_entry_checked_immutable_types]
QED

Theorem prefix_entry_checked_constants_no_clobber[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  constants_do_not_clobber_bare_globals [(NONE,tops)] (FEMPTY |+ ((NONE,name),ty))
Proof
  strip_tac >> drule prefix_entry_checked_decl_keys >> strip_tac >>
  rw[constants_do_not_clobber_bare_globals_def, FLOOKUP_UPDATE] >>
  gvs[] >> metis_tac[module_immutable_constant_names_distinct]
QED

Theorem prefix_entry_default_admissible[local]:
  (!tv. well_formed_type_value tv ==>
        immutable_value_admissible tv (default_value tv)) /\
  (!tvs. EVERY well_formed_type_value tvs ==>
         immutable_tuple_admissible tvs (MAP default_value tvs)) /\
  (!fts. EVERY (well_formed_type_value o SND) fts ==>
         immutable_fields_admissible fts (MAP (\(id,t). (id, default_value t)) fts))
Proof
  ho_match_mp_tac type_memory_size_ind >>
  rw[vyperTypingTheory.well_formed_type_value_def,
     default_value_def, default_value_tuple_MAP, default_value_struct_MAP,
     immutable_value_admissible_def, prefix_entry_zero_address_bytes] >> gvs[ETA_THM]
QED

Theorem prefix_entry_checked_type_size[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  evaluate_type (type_env tops) ty = SOME tv ==>
  type_memory_size tv = type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty
Proof
  strip_tac >> drule_all prefix_entry_checked_decl >> strip_tac >>
  `abi_decoder_coherent
    (build_compile_env tops External Payable "" [] NoneT [] F) (type_env tops)
    (build_compile_env tops External Payable "" [] NoneT [] F).ce_struct_fields ty tv` by
    (irule abi_caller_coherent >> metis_tac[]) >>
  drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
  simp[abiDecoderCoherenceTheory.abi_decoder_header_def,
       GSYM type_mem_bytes_type_memory_bytes, build_compile_env_ce_struct_fields]
QED

Theorem prefix_entry_evaluated_default_admissible[local]:
  evaluate_type env ty = SOME tv ==> immutable_value_admissible tv (default_value tv)
Proof
  strip_tac >> irule (cj 1 prefix_entry_default_admissible) >>
  metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
QED

Theorem prefix_entry_constants_preserve_lookup[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  evaluate_all_constants cx am addr [(NONE,tops)] = SOME am_c /\
  FLOOKUP (get_source_immutables NONE
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) name = SOME x ==>
  FLOOKUP (get_source_immutables NONE
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) name = SOME x
Proof
  strip_tac >> drule_all prefix_entry_checked_constants_no_clobber >> strip_tac >>
  irule evaluate_all_constants_preserves_bare_global_lookup_type >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`FEMPTY |+ ((NONE,name),ty)`, `ty`] >>
  gvs[constants_do_not_clobber_bare_globals_def, FLOOKUP_UPDATE]
QED

Theorem prefix_entry_initialized_zero_section[local]:
  deploy_typing_ok tops am tx /\
  initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms /\
  evaluate_all_constants (deploy_evaluation_context tops am tx)
    (am with <| immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,[]) |>)
    tx.target [(NONE,tops)] = SOME am_c ==>
  immutables_section_rel tops
    (case ALOOKUP am_c.immutables tx.target of SOME m => m | NONE => [])
    (REPLICATE (imm_len tops) 0w)
Proof
  strip_tac >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    gvs[deploy_typing_ok_def] >>
  pop_assum strip_assume_tac >>
  irule prefix_entry_zero_section >> rpt gen_tac >> strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  drule_all prefix_entry_checked_initial_lookup >> strip_tac >>
  `v = default_value tv` by metis_tac[prefix_entry_initial_defaults] >> gvs[] >>
  qexists `tv` >> conj_tac
  >- (irule prefix_entry_constants_preserve_lookup >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[prefix_entry_evaluated_default_admissible] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  drule prefix_entry_checked_type_size >> disch_then irule >> conj_tac
  >- (qpat_x_assum `evaluate_type _ _ = SOME tv` mp_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  qexistsl [`name`, `slot`, `vis`] >> simp[]
QED

Theorem prefix_entry_start_zero_section:
  !tops am tx mut nr body am_c es0.
  deploy_typing_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) ==>
  immutables_section_rel tops
    (case ALOOKUP am_c.immutables tx.target of SOME m => m | NONE => [])
    (REPLICATE (imm_len tops) 0w)
Proof
  rpt gen_tac >> strip_tac >> fs[deploy_ctor_start_def] >>
  irule prefix_entry_initialized_zero_section >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem prefix_entry_section_memory_relation[local]:
  immutable_section_layout cenv tops /\
  immutables_section_rel tops imms section /\
  ALOOKUP es.immutables addr = SOME imms /\
  mem_bytes_at 0 (LENGTH section) ss.vs_memory = section ==>
  immutables_rel cenv addr NONE T es ss
Proof
  strip_tac >> simp[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `immutable_section_layout _ _`
    (mp_tac o REWRITE_RULE [immutable_section_layout_def]) >>
  disch_then drule >> strip_tac >>
  drule_all immutables_section_rel_lookup >> strip_tac >>
  `mem_bytes_at byte_offset (type_memory_size tv) section =
   mem_bytes_at byte_offset (type_memory_size tv) ss.vs_memory` by
    (irule (cj 1 mem_bytes_at_agree_window) >>
     qexistsl [`LENGTH section`, `0`] >> gvs[mem_bytes_at_def, TAKE_APPEND]) >>
  gvs[] >>
  irule val_in_memory_mem_agree >>
  conj_tac >- metis_tac[immutable_admissible_val_wf] >>
  qexistsl [`type_memory_size tv`, `section`] >>
  simp[immutable_admissible_val_wf]
QED

Theorem prefix_entry_prefix_bytes_agree[local]:
  (!p. p < cap ==> mem_bytes_at p 1 mem = mem_bytes_at p 1 mem') ==>
  mem_bytes_at 0 cap mem = mem_bytes_at 0 cap mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >>
  rpt strip_tac >> first_x_assum drule >>
  disch_then (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[EL_mem_bytes_at]
QED

Theorem prefix_entry_empty_zero_section[local]:
  mem_bytes_at 0 cap ([]:word8 list) = REPLICATE cap 0w
Proof
  simp[mem_bytes_at_def]
QED

Theorem prefix_entry_zero_prefix_section[local]:
  (!p. p < cap ==> mem_bytes_at p 1 ss.vs_memory = mem_bytes_at p 1 []) ==>
  mem_bytes_at 0 cap ss.vs_memory = REPLICATE cap 0w
Proof
  strip_tac >>
  `mem_bytes_at 0 cap ss.vs_memory = mem_bytes_at 0 cap []` by
    (irule prefix_entry_prefix_bytes_agree >> simp[]) >>
  simp[prefix_entry_empty_zero_section]
QED

Theorem prefix_entry_zero_memory_immutables:
  !tops am tx mut nr body am_c es0 cenv addr ss es.
  deploy_typing_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  immutable_section_layout cenv tops /\ addr = tx.target /\
  es.immutables = am_c.immutables /\
  (!p. p < imm_len tops ==>
    mem_bytes_at p 1 ss.vs_memory = mem_bytes_at p 1 []) ==>
  immutables_rel cenv addr NONE T es ss
Proof
  rpt gen_tac >> strip_tac >>
  drule_all prefix_entry_start_zero_section >> strip_tac >>
  drule prefix_entry_zero_prefix_section >> strip_tac >>
  Cases_on `ALOOKUP es.immutables addr`
  >- simp[immutables_rel_def] >>
  irule prefix_entry_section_memory_relation >>
  qexistsl [`x`, `REPLICATE (imm_len tops) 0w`, `tops`] >> gvs[]
QED
