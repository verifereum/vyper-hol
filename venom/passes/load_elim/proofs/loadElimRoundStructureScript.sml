Theory loadElimRoundStructure
Ancestors
  loadElimPrependIndex loadElimTargetWrites loadElimOriginHelpers
  loadElimDefs loadElimKeyShapeInvariant passSharedDefs
  analysisSimDefs passSimulationDefs passSimulationProps cfgDefs venomInst venomExecSemantics
  list rich_list indexedLists ctxLookupAgreeHelpers

Theorem le_configured_inst_successors:
  le_configured_context ctx ==>
  get_successors (load_elim_inst ctx actions ll inst) = get_successors inst
Proof
  strip_tac >>
  Cases_on `load_elim_inst ctx actions ll inst = inst` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def,
      get_successors_def, mk_assign_inst_def, mk_nop_inst_def, is_terminator_def]
QED

Theorem le_inst_no_memtop:
  inst.inst_opcode <> MEMTOP ==>
  (load_elim_inst ctx actions ll inst).inst_opcode <> MEMTOP
Proof
  strip_tac >>
  Cases_on `load_elim_inst ctx actions ll inst = inst` >- simp[] >>
  drule_at (Pat `transformed <> inst`) load_elim_inst_changed >>
  disch_then (qspecl_then [`ll`, `ctx`, `actions`] mp_tac) >>
  simp[] >> strip_tac >> gvs[mk_assign_inst_def, mk_nop_inst_def]
QED

Theorem le_phi_list_successors:
  !ys. EVERY (\i. i.inst_opcode = PHI) ys ==>
    (case ys of [] => [] | _ => get_successors (LAST ys)) = []
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `ys` >> gvs[LAST_CONS_cond, get_successors_def, is_terminator_def]
QED

Theorem le_insert_phi_successors:
  !xs ys. EVERY (\i. i.inst_opcode = PHI) ys ==>
    (case TAKE (phi_prefix_length xs) xs ++ ys ++ DROP (phi_prefix_length xs) xs of
       [] => [] | zs => get_successors (LAST zs)) =
    (case xs of [] => [] | _ => get_successors (LAST xs))
Proof
  Induct >- (gen_tac >> strip_tac >>
    drule le_phi_list_successors >>
    Cases_on `ys` >> simp[phi_prefix_length_def]) >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (first_x_assum (qspec_then `ys` mp_tac) >> simp[] >>
      simp[phi_prefix_length_def] >>
      Cases_on `xs` >- (simp[phi_prefix_length_def] >>
        Cases_on `ys` >> simp[LAST_CONS_cond, get_successors_def, is_terminator_def]) >>
      qmatch_goalsub_abbrev_tac `TAKE n (h'::t)` >>
      `0 < LENGTH (TAKE n (h'::t) ++ ys ++ DROP n (h'::t))` by
        (simp[LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac) >>
      Cases_on `TAKE n (h'::t) ++ ys ++ DROP n (h'::t)` >>
      gvs[LAST_CONS_cond]) >>
  simp[phi_prefix_length_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  Cases_on `ys` >> simp[LAST_CONS_cond] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, listTheory.LAST_APPEND_CONS] >>
  simp[LAST_CONS_cond]
QED

Theorem le_mapi_successors:
  !xs lats. le_configured_context ctx ==>
    (case MAPi (\n i. load_elim_inst ctx actions (lats n) i) xs of
       [] => [] | zs => get_successors (LAST zs)) =
    (case xs of [] => [] | _ => get_successors (LAST xs))
Proof
  Induct >> simp[MAPi_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `lats o SUC` mp_tac) >>
  Cases_on `xs` >> simp[MAPi_def, combinTheory.o_DEF, le_configured_inst_successors]
QED

Theorem le_prepend_bb_succs:
  le_configured_context ctx ==>
  bb_succs (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
    (\ll inst. [load_elim_inst ctx actions ll inst]) bb) = bb_succs bb
Proof
  strip_tac >>
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
       flat_mapi_singleton] >>
  mp_tac (Q.SPECL [`MAPi (\n i. load_elim_inst ctx actions
      (df_at NONE result bb.bb_label n) i) bb.bb_instructions`,
      `phis_for_block actions bb.bb_label`] le_insert_phi_successors) >>
  simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER] >>
  drule le_mapi_successors >>
  disch_then (qspecl_then [`actions`, `bb.bb_instructions`,
    `\n. df_at NONE result bb.bb_label n`] mp_tac) >>
  simp[bb_succs_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem le_cfg_map_transform:
  (!bb. (bt bb).bb_label = bb.bb_label) /\
  (!bb. bb_succs (bt bb) = bb_succs bb) ==>
  cfg_analyze (function_map_transform bt fn) = cfg_analyze fn
Proof
  strip_tac >>
  `!bbs. build_succs (MAP bt bbs) = build_succs bbs` by
    simp[build_succs_def, init_succs_def, FOLDL_MAP, combinTheory.o_DEF] >>
  `!bbs succs. build_preds (MAP bt bbs) succs = build_preds bbs succs` by
    simp[build_preds_def, init_preds_def, FOLDL_MAP, combinTheory.o_DEF] >>
  simp[cfg_analyze_def, function_map_transform_def, MAP_MAP_o,
       combinTheory.o_DEF, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

Theorem le_prepend_cfg:
  le_configured_context ctx ==>
  cfg_analyze (analysis_function_transform_prepend NONE result (load_phi_prepend actions)
    (\ll inst. [load_elim_inst ctx actions ll inst]) fn) = cfg_analyze fn
Proof
  strip_tac >> simp[analysis_function_transform_prepend_def] >>
  irule le_cfg_map_transform >>
  simp[le_prepend_bb_succs, analysis_block_transform_prepend_def]
QED

Theorem le_round_cfg:
  le_configured_context ctx ==>
  cfg_analyze (load_elim_one ctx g fn) = cfg_analyze fn
Proof
  simp[load_elim_one_def, le_prepend_cfg]
QED

Theorem le_round_entry:
  fn_entry_label (load_elim_one ctx g fn) = fn_entry_label fn
Proof
  simp[load_elim_one_def, analysis_function_transform_prepend_def,
       function_map_transform_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[analysis_block_transform_prepend_def]
QED

Theorem le_prepend_no_memtop:
  EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions ==>
  EVERY (\i. i.inst_opcode <> MEMTOP)
    (analysis_block_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) bb).bb_instructions
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> MEMTOP)
    (MAPi (\n i. load_elim_inst ctx actions (df_at NONE result bb.bb_label n) i)
      bb.bb_instructions)` by
    (gvs[EVERY_EL, LENGTH_MAPi, EL_MAPi] >> metis_tac[le_inst_no_memtop]) >>
  simp[analysis_block_transform_prepend_def, load_phi_prepend_def,
       flat_mapi_singleton] >>
  reverse conj_tac >- metis_tac[EVERY_DROP] >>
  conj_tac >- metis_tac[EVERY_TAKE] >>
  simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER]
QED

Theorem le_prepend_function_no_memtop:
  EVERY (\i. i.inst_opcode <> MEMTOP) (fn_insts fn) ==>
  EVERY (\i. i.inst_opcode <> MEMTOP)
    (fn_insts (analysis_function_transform_prepend NONE result (load_phi_prepend actions)
      (\ll inst. [load_elim_inst ctx actions ll inst]) fn))
Proof
  simp[analysis_function_transform_prepend_def, function_map_transform_def,
       fn_insts_def, fn_insts_EVERY_block, EVERY_MAP] >>
  strip_tac >> irule listTheory.EVERY_MONOTONIC >>
  qexists_tac `\bb. EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions` >>
  simp[le_prepend_no_memtop]
QED

Theorem le_round_no_memtop:
  le_configured_context ctx /\
  EVERY (\i. i.inst_opcode <> MEMTOP) (fn_insts fn) ==>
  EVERY (\i. i.inst_opcode <> MEMTOP) (fn_insts (load_elim_one ctx g fn))
Proof
  simp[load_elim_one_def, le_prepend_function_no_memtop]
QED
