(* Frame code and raw free-memory headroom for a linked constructor. *)
Theory linkedDeployEntry
Ancestors
  e2eDeployModsDefs e2eEntry bodyInvSplit compileUnit
  vyperCompiler lowerDloadDefs venomLayout vyperContext arithmetic words

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
