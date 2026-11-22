(* Frame code and raw free-memory headroom for a linked constructor. *)
Theory linkedDeployEntry
Ancestors
  e2eDeployModsDefs e2eEntry bodyInvSplit compileUnit
  vyperCompiler lowerDloadDefs venomLayout vyperContext arithmetic words
  e2eDefs asmFrameRel asmDataSuffixProps codegenEntryRel codegenLabelDisciplined
  codegenRel contextCodegenRel contextPlanLayoutProps deployFrameReplay
  frameRel finite_map list loweringStateRelDefs callTrace venomState vyperArith

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
