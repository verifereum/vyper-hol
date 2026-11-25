(* The linked runtime's source, Venom and assembly entry states. *)
Theory linkedCallEntry
Ancestors
  e2eModsDefs e2eDefs e2eEntry sourceUnitExecutionMods loweringStateRelDefs
  vyperLoweringCorrect vyperCompiler lowerDloadDefs venomLayout
  asmFrameRel asmDataSuffixProps codegenEntryRel codegenLabelDisciplined
  contextCodegenRel codegenRel frameRel vfmExecution vfmExecutionProp
  venomState arithmetic words vyperArith finite_map list rich_list

Theorem opt_entry_initial_venom_state_rel_mods:
  !mods exps prog prog' am tx es cplan.
    call_state_rel_mods mods exps (assemble prog') am tx es ==>
    initial_venom_state_rel_mods mods am tx (opt_entry_state_own prog prog' cplan es)
Proof
  rpt gen_tac >> strip_tac >>
  fs[call_state_rel_mods_def, frame_tx_rel_def, world_rel_def,
     installed_code_rel_mods_def] >>
  simp[initial_venom_state_rel_mods_def, opt_entry_state_own_def,
       entry_venom_state_frame_fields, entry_venom_state_fresh] >>
  simp[venom_env_rel_def, call_ctx_rel_def] >>
  simp[entry_venom_state_def] >>
  fs[tx_block_fields_rel_def] >>
  conj_tac
  >- (gen_tac >>
      Cases_on `n < tx.block_number /\ tx.block_number <= n + 256` >> gvs[] >>
      `tx.block_number - (n + 1) < 256` by decide_tac >>
      simp[EL_TAKE, LENGTH_TAKE_EQ] >> rw[] >> gvs[] >> decide_tac) >>
  qpat_assum `assemble prog' ++ section = tx.code` (fn code =>
    REWRITE_TAC[GSYM code]) >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem opt_entry_asm_rels_own_mods:
  !mods exps prog prog' am tx es cplan.
    call_state_rel_mods mods exps (assemble prog') am tx es /\
    assemble prog' <> [] ==>
    (opt_entry_state_own prog prog' cplan es).vs_code =
      assemble prog' ++ (opt_entry_state_own prog prog' cplan es).vs_data_section /\
    codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog
      (opt_entry_state_own prog prog' cplan es)
      (entry_asm_state (opt_entry_state_own prog prog' cplan es) es) /\
    asm_frame_rel prog' (opt_entry_state_own prog prog' cplan es).vs_data_section es
      (entry_asm_state (opt_entry_state_own prog prog' cplan es) es) es
Proof
  rpt gen_tac >> strip_tac >>
  fs[call_state_rel_mods_def, installed_code_rel_mods_def,
     frame_tx_rel_def, frame_fresh_def, evm_state_ok_def] >>
  `ctxt.msgParams.parsed = parse_code 0 FEMPTY ctxt.msgParams.code` by
    gvs[wf_state_def, wf_context_def] >>
  `es.txParams.blockNumber < dimword (:256)` by
    (fs[tx_block_fields_rel_def, world_rel_def, tx_env_ok_def] >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  drule_all entry_venom_state_evm_environment >>
  disch_then (qspecl_then [`prog'`, `cplan`] strip_assume_tac) >>
  simp[opt_entry_state_own_def, entry_venom_state_frame_fields, DROP_LENGTH_APPEND] >>
  conj_tac
  >- (simp[codegen_asm_entry_rel_reloc_def, entry_asm_state_def, shared_state_rel_def,
           venom_asm_terminal_rel_def, entry_venom_state_fresh, FLOOKUP_o_f] >>
      simp[entry_venom_state_def, init_venom_state_def, context_memory_rel_def] >>
      gen_tac >> Cases_on `FLOOKUP (lo_reloc prog prog') l` >> simp[]) >>
  simp[asm_frame_rel_def, asm_evm_rel_def, entry_asm_state_def, data_suffix_assemble,
       entry_venom_state_fresh, entry_venom_state_created_in_tx, asm_pc_to_offset_def,
       relationTheory.RTC_REFL] >>
  gvs[msg_ctx_rel_def, tx_ctx_rel_def, block_ctx_rel_def, blockhash_rel_def,
      account_already_created_def, NULL_EQ] >>
  qpat_assum `assemble prog' ++ section = tx.code`
    (fn code => once_rewrite_tac[GSYM code]) >>
  simp[entry_venom_state_frame_fields, CONJ_ASSOC]
QED

Theorem call_raw_fmp_exists_mods:
  lowering_context_ok unit.cu_context /\
  cplan.cp_initial_fmp < 2 ** 254 ==>
  ?fmp:bytes32.
    w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp
Proof
  strip_tac >>
  qabbrev_tac `need = unit_alloca_budget unit.cu_context +
     32 * ctx_dload_count unit.cu_context` >>
  `need < 2 ** 254` by
    (drule lowering_context_ok_static_headroom >>
     simp[Abbr `need`, ctx_dload_count_def, FILTER_FLAT, LENGTH_FLAT,
          MAP_MAP_o, combinTheory.o_DEF]) >>
  qabbrev_tac `n = MAX cplan.cp_initial_fmp need` >>
  `n < 2 ** 254` by simp[Abbr `n`, MAX_DEF] >>
  `n < dimword (:256) /\ cplan.cp_initial_fmp < dimword (:256)` by
    (fs[dimword_def, dimindex_256] >> decide_tac) >>
  qexists_tac `n2w n` >>
  simp[opt_entry_state_own_def, entry_venom_state_def, w2n_n2w] >>
  fs[Abbr `n`, MAX_DEF] >> decide_tac
QED
