Theory o1ContractSimplifyCfgSrcHeadroom
Ancestors
  simplifyCfgInvariant simplifyCfgCorrectness lowerDloadDefs o1PassLift
  unitMemInv list rich_list simplifyCfgDefs simplifyCfgShape cfgTransform
  venomWf venomInst pred_set arithmetic dftCorrectness passSimulationProofs

Theorem simplify_cfg_fn_dload_ids:
  MEM i (fn_insts (simplify_cfg_fn f)) /\ i.inst_opcode = DLOAD ==>
  MEM i.inst_id (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = DLOAD) (fn_insts f)))
Proof
  `EVERY (\i. i.inst_opcode = DLOAD ==>
     MEM i.inst_id (MAP (\j. j.inst_id)
       (FILTER (\j. j.inst_opcode = DLOAD) (fn_insts f))))
     (fn_insts (FST (simplify_cfg_fn_with_labels f)))` suffices_by
    (simp[simplify_cfg_fn_def, EVERY_MEM] >> metis_tac[]) >>
  irule simplify_cfg_fn_with_labels_every >>
  simp[fix_phi_inst_id, update_phi_bypass_id, canon_jnz_inst_id,
       update_phi_bypass_opcode, subst_label_inst_def,
       subst_block_labels_inst_def] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `(canon_jnz_inst i) = i` by
        (irule canon_jnz_inst_not_jmp >> simp[]) >> gvs[]) 
  >- (rpt strip_tac >>
      `i.inst_opcode = DLOAD` by
        (irule fix_phi_inst_opcode_source >> simp[] >> qexists_tac `ps` >> simp[]) >>
      gvs[]) 
  >- (rpt gen_tac >> Cases_on `is_block_label_opcode i.inst_opcode` >>
      simp[subst_label_map_inst_def]) >>
  simp[EVERY_MEM, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem simplify_cfg_fn_dload_count_le:
  wf_function f ==>
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts (simplify_cfg_fn f))) <=
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f))
Proof
  strip_tac >>
  `wf_function (simplify_cfg_fn f)` by
    (irule simplify_cfg_preserves_wf_function >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts (simplify_cfg_fn f)))` by
    gvs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def, passSimulationProofsTheory.fn_insts_blocks_flat,
        MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  drule all_distinct_map_filter >>
  disch_then (qspec_then `\i. i.inst_opcode = DLOAD` assume_tac) >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT ids` >>
  qabbrev_tac `orig = MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts f))` >>
  `set ids SUBSET set orig` by
    (simp[Abbr `ids`, Abbr `orig`, SUBSET_DEF, MEM_MAP, MEM_FILTER] >>
     rpt strip_tac >> drule_all simplify_cfg_fn_dload_ids >>
     simp[MEM_MAP, MEM_FILTER]) >>
  `CARD (set ids) <= CARD (set orig)` by
    (irule CARD_SUBSET >> simp[]) >>
  `CARD (set ids) = LENGTH ids` by simp[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `CARD (set orig) <= LENGTH orig` by simp[CARD_LIST_TO_SET] >>
  gvs[Abbr `ids`, Abbr `orig`]
QED

Theorem simplify_cfg_ctx_dload_count_le:
  EVERY wf_function C.ctx_functions /\
  C'.ctx_functions = MAP simplify_cfg_fn C.ctx_functions ==>
  ctx_dload_count C' <= ctx_dload_count C
Proof
  simp[ctx_dload_count_def] >> strip_tac >> gvs[MAP_MAP_o] >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  qpat_x_assum `C'.ctx_functions = _` kall_tac >>
  qspec_tac (`C.ctx_functions`, `fs`) >>
  Induct >> simp[] >> rpt strip_tac >>
  drule simplify_cfg_fn_dload_count_le >>
  gvs[combinTheory.o_DEF] >> decide_tac
QED

Theorem dload_headroom_fixed_corr_closed_rf:
  mem_corr_closed_rf (\ctx fn inst s. dload_headroom_ok C fn inst s)
Proof
  irule mem_corr_closed_rf_intro >>
  simp[mem_corr_closed_def, mem_corr_def, dload_headroom_ok_def]
QED

Theorem dload_headroom_mem_inv_freeze:
  mem_inv dload_headroom_ok C vs ==>
  mem_inv (\ctx fn inst s. dload_headroom_ok C fn inst s) C vs
Proof
  strip_tac >> irule mem_inv_mono >>
  qexists_tac `dload_headroom_ok` >> simp[]
QED

Theorem dload_headroom_mem_inv_decrease:
  ctx_dload_count C' <= ctx_dload_count C /\
  mem_inv (\ctx fn inst s. dload_headroom_ok C fn inst s) C' vs ==>
  mem_inv dload_headroom_ok C' vs
Proof
  strip_tac >> irule mem_inv_mono >>
  qexists_tac `\ctx fn inst s. dload_headroom_ok C fn inst s` >>
  simp[dload_headroom_ok_def] >> rpt strip_tac >> decide_tac
QED
