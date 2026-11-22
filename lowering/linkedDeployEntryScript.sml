(* Frame code and raw free-memory headroom for a linked constructor. *)
Theory linkedDeployEntry
Ancestors
  e2eDeployModsDefs e2eEntry bodyInvSplit compileUnit
  vyperCompiler lowerDloadDefs venomLayout vyperContext arithmetic words
  e2eDefs asmFrameRel asmDataSuffixProps codegenEntryRel codegenLabelDisciplined
  codegenRel contextCodegenRel contextPlanLayoutProps deployFrameReplay
  frameRel finite_map list loweringStateRelDefs callTrace venomState vyperArith
  ctorDeployInitcode ctorDeployDefs compileVyper compileEnv abiTypeBoundProps
  vyperTypeABI vyperTyping vyperABI vyperAST moduleLowering constSubst constSubstMods
  vyperInterpreter pair option rich_list

Theorem deploy_own_txp_identity_mods:
  !mods exps bc am tx prog prog' cplan es.
    deploy_state_rel_mods mods exps bc am tx es ==>
    tx with code := (opt_entry_state_own prog prog' cplan es).vs_code = tx
Proof
  rw[opt_entry_state_own_def, entry_venom_state_frame_fields,
     call_txn_component_equality] >>
  gvs[deploy_state_rel_mods_def]
QED

Theorem deploy_raw_fmp_exists_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME dunit /\
  cplan.cp_initial_fmp < 2 ** 254 ==>
  ?fmp:bytes32.
    w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len_mods mods + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp
Proof
  strip_tac >>
  qabbrev_tac `need = imm_len_mods mods + unit_alloca_budget dunit.cu_context +
     32 * ctx_dload_count dunit.cu_context` >>
  `need < 2 ** 254` by
    (qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
     simp[lower_vyper_deploy_unit_mods_def, LET_THM] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >>
     drule run_deploy_lowering_static_headroom >>
     simp[Abbr `need`, imm_len_mods_def, ctx_dload_count_def,
          rich_listTheory.FILTER_FLAT, rich_listTheory.LENGTH_FLAT,
          listTheory.MAP_MAP_o, combinTheory.o_DEF] >> decide_tac) >>
  qabbrev_tac `n = MAX cplan.cp_initial_fmp need` >>
  `n < 2 ** 254` by simp[Abbr `n`, MAX_DEF] >>
  `n < dimword (:256) /\ cplan.cp_initial_fmp < dimword (:256)` by
    (fs[dimword_def, dimindex_256] >> decide_tac) >>
  qexists_tac `n2w n` >>
  simp[opt_entry_state_own_def, entry_venom_state_def, w2n_n2w] >>
  fs[Abbr `n`, MAX_DEF] >> decide_tac
QED

Theorem opt_deploy_asm_rels_own_mods:
  !mods exps prog prog' am tx es cplan vs.
    deploy_state_rel_mods mods exps (assemble prog') am tx es /\
    assemble prog' <> [] /\
    vs = (opt_entry_state_own prog prog' cplan es with vs_alloca_next := imm_len_mods mods) ==>
    vs.vs_code = assemble prog' ++ vs.vs_data_section /\
    codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog vs
      (entry_asm_state vs (shadow_root es)) /\
    asm_frame_rel prog' vs.vs_data_section (shadow_root es)
      (entry_asm_state vs (shadow_root es)) (shadow_root es)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `wf_state (shadow_root es)` by fs[deploy_state_rel_mods_def, shadow_root_wf_state] >>
  fs[deploy_state_rel_mods_def] >>
  `frame_obs (shadow_root es) = frame_obs es` by
    (irule shadow_root_frame_obs >> simp[]) >>
  `call_trace (shadow_root es) = call_trace es /\
   gas_readings (shadow_root es) = gas_readings es` by
    simp[call_trace_def, gas_readings_def] >>
  `es.txParams.blockNumber < dimword (:256)` by
    (fs[tx_block_fields_rel_def, tx_env_ok_def] >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  simp[codegen_asm_entry_rel_reloc_def, asm_frame_rel_def, asm_evm_rel_def,
       entry_asm_state_def, shared_state_rel_def, venom_asm_terminal_rel_def,
       opt_entry_state_own_def, data_suffix_assemble, asm_pc_to_offset_zero,
       entry_venom_state_frame_fields, FLOOKUP_o_f,
       shadow_root_def, shadow_root_contexts_def] >>
  simp[entry_venom_state_def] >>
  simp[init_venom_state_def, w2n_n2w, DROP_APPEND] >>
  fs[context_memory_rel_def, CONJ_ASSOC] >>
  gen_tac >> Cases_on `FLOOKUP (lo_reloc prog prog') l` >> simp[]
QED

Theorem constructor_args_size_bounded_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME unit /\
  sfields_tenv_consistent (make_struct_fields_map_mods mods)
    (type_env_all_modules mods) /\
  constructor_args_encode_mods mods tx bs ==>
  LENGTH bs < 2 ** 128
Proof
  strip_tac >>
  qpat_x_assum `constructor_args_encode_mods _ _ _` mp_tac >>
  simp[constructor_args_encode_mods_def, IS_SOME_EXISTS] >> strip_tac >> gvs[] >>
  drule bind_arguments_values_typed >> strip_tac >>
  drule_all (cj 2 vyper_to_abi_enc_length_bound) >> strip_tac >>
  `EVERY (\t. IS_SOME (evaluate_type (type_env_all_modules mods) t))
     (MAP SND args)` by
    (fs[EVERY_MEM, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all abi_size_bound_tuple_typed >> strip_tac >>
  `vyper_abi_size_bound (type_env_all_modules mods) (TupleT (MAP SND args)) =
   vyper_abi_size_bound_list (type_env_all_modules mods) (MAP SND args)` by
    simp[Once vyper_abi_size_bound_def] >>
  `abi_size_bound (make_struct_fields_map_mods mods) (TupleT (MAP SND args)) <
     2 ** 128` suffices_by (strip_tac >> fs[] >> decide_tac) >>
  qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_mods_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[bool_case_eq] >> strip_tac >>
  qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
  simp[classify_functions_unit_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qspecl_then [`main_module mods`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >>
  simp[classify_functions_def] >>
  Cases_on `ctor` >> simp[]
  >- (strip_tac >> gvs[abi_size_bound_def]) >>
  rename1 `ctor_named_init (OPTION_MAP _ (SOME raw_ctor))` >>
  PairCases_on `raw_ctor` >>
  gvs[subst_consts_fn_mods_def, subst_consts_fn_def, ctor_named_init_def] >>
  strip_tac >> gvs[fn_allocs_ok_unit_def, build_compile_env_unit_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_entry_code_layout_mods:
  deploy_state_rel_mods mods exps (assemble prog') am tx es /\
  (!bs. constructor_args_encode_mods mods tx bs ==> LENGTH bs < 2 ** 128) /\
  FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog')) /\
  LENGTH (assemble prog') < 65536 ==>
  code_layout_valid (opt_entry_state_own prog prog' cplan es)
Proof
  strip_tac >>
  `?bs. (FST (HD es.contexts)).msgParams.code = assemble prog' ++ bs /\
        constructor_args_encode_mods mods tx bs` by
    fs[deploy_state_rel_mods_def] >>
  `LENGTH bs < 2 ** 128` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  simp[code_layout_valid_def, opt_entry_state_own_def, entry_venom_state_frame_fields,
       FLOOKUP_o_f, DROP_LENGTH_APPEND, dimword_def, dimindex_256] >>
  qpat_assum `LENGTH bs < 2 ** 128`
    (assume_tac o REWRITE_RULE [EVAL ``2 ** 128 : num``]) >>
  decide_tac
QED
