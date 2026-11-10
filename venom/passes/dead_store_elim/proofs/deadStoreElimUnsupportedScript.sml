Theory deadStoreElimUnsupported
Ancestors
  deadStoreElimDefs pred_set While

Theorem dse_unsupported_memory_def:
  sp NOTIN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  ~is_memory_def_opcode sp op
Proof
  Cases_on `sp` >> simp[is_memory_def_opcode_def]
QED

Theorem all_dead_stores_unsupported:
  sp NOTIN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  all_dead_stores ids cfg aliases bp sp fn ==> ids = {}
Proof
  strip_tac >>
  `!op. ~is_memory_def_opcode sp op` by
    (gen_tac >> irule dse_unsupported_memory_def >> simp[]) >>
  fs[all_dead_stores_def, EXTENSION]
QED

Theorem dse_function_space_unsupported:
  sp NOTIN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} /\
  (!fn'. all_dead_stores (analysis_fn sp fn') (cfg_analyze fn') FEMPTY
          (bp_analyze (cfg_analyze fn') fn') sp fn') ==>
  dse_function_space analysis_fn sp fn = clear_nops_function fn
Proof
  strip_tac >>
  `analysis_fn sp fn = {}` by
    (irule all_dead_stores_unsupported >> metis_tac[]) >>
  `dse_iterate (analysis_fn sp) sp fn = SOME fn` by
    (rewrite_tac[dse_iterate_def] >> once_rewrite_tac[OWHILE_THM] >> simp[]) >>
  simp[dse_function_space_def]
QED
