(* Non-SSA block and function shape transport. *)
Theory dftLifting
Ancestors
  dftShape dftCorrectness dftWf dftNonSsa dftStructural dftDefs
  unitLabelMapIdentity irSupply
  venomWf venomInst unitShapeDefs passSharedDefs stackPlanTypes list rich_list arithmetic
Libs
  BasicProvers

Theorem dft_block_phi_prefix:
  bb_well_formed bb ==>
  !i j. i < j /\ j < LENGTH (dft_block order bb).bb_instructions /\
    (EL j (dft_block order bb).bb_instructions).inst_opcode = PHI ==>
    (EL i (dft_block order bb).bb_instructions).inst_opcode = PHI
Proof
  strip_tac >> simp[dft_block_def, LET_THM] >>
  qabbrev_tac `ps = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `sched = schedule_from_entries bb.bb_instructions order
    (build_eda bb.bb_instructions) (build_offspring_map bb.bb_instructions order)
    (entry_instructions bb.bb_instructions order (build_eda bb.bb_instructions))` >>
  rpt strip_tac >> Cases_on `j < LENGTH ps`
  >- (`i < LENGTH ps` by decide_tac >> gvs[EL_APPEND1] >>
      qspecl_then [`\i. is_pseudo i.inst_opcode`, `bb.bb_instructions`, `i`, `j`]
        mp_tac filter_el_mono >> simp[GSYM (Abbr `ps`)] >> strip_tac >>
      gvs[bb_well_formed_def] >> metis_tac[]) >>
  `j - LENGTH ps < LENGTH sched` by decide_tac >>
  `MEM (EL (j - LENGTH ps) sched) sched` by simp[EL_MEM] >>
  `~is_pseudo (EL (j - LENGTH ps) sched).inst_opcode` by
    (irule (INST_TYPE [alpha |-> ``:instruction``] (cj 2 schedule_output_from_block)) >>
     qexistsl_tac [`bb.bb_instructions`, `build_eda bb.bb_instructions`,
       `entry_instructions bb.bb_instructions order (build_eda bb.bb_instructions)`,
       `build_offspring_map bb.bb_instructions order`, `order`] >>
     simp[build_eda_wf, entry_instructions_mem, Abbr `sched`]) >>
  gvs[EL_APPEND2, is_pseudo_def]
QED

Theorem dft_block_unique_terminator:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  !k. k < LENGTH (dft_block order bb).bb_instructions /\
    is_terminator (EL k (dft_block order bb).bb_instructions).inst_opcode ==>
    k = PRE (LENGTH (dft_block order bb).bb_instructions)
Proof
  strip_tac >> drule_all dft_block_last >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions)` by
    (irule dft_block_distinct_ids >> simp[]) >>
  rpt strip_tac >>
  qabbrev_tac `out = (dft_block order bb).bb_instructions` >>
  `MEM (EL k out) out` by simp[EL_MEM] >>
  `?src. MEM src bb.bb_instructions /\
    (EL k out).inst_id = src.inst_id /\ is_terminator src.inst_opcode` by
    (qpat_x_assum `MEM _ out` mp_tac >> simp[Abbr `out`] >>
     disch_then (strip_assume_tac o MATCH_MP dft_block_instruction_source) >>
     gvs[flip_operands_inst_id]
     >- metis_tac[] >>
     qexists_tac `j` >> simp[] >>
     qpat_x_assum `is_terminator _` mp_tac >>
     Cases_on `j.inst_operands` >> simp[flip_operands_def] >>
     Cases_on `t` >> simp[flip_operands_def] >>
     Cases_on `t'` >> simp[flip_operands_def] >>
     Cases_on `j.inst_opcode` >>
     simp[passSharedDefsTheory.is_comparator_def,
          flip_comparison_opcode_def, is_terminator_def]) >>
  `?n. n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = src` by
    metis_tac[MEM_EL] >>
  `n = PRE (LENGTH bb.bb_instructions)` by
    (gvs[bb_well_formed_def] >> metis_tac[]) >>
  `src = LAST bb.bb_instructions` by
    (gvs[bb_well_formed_def, LAST_EL] >>
     Cases_on `bb.bb_instructions` >> gvs[]) >>
  `0 < LENGTH out` by (Cases_on `out` >> gvs[]) >>
  `EL k (MAP (\i. i.inst_id) out) =
   EL (PRE (LENGTH out)) (MAP (\i. i.inst_id) out)` by
    simp[EL_MAP, GSYM LAST_EL] >>
  drule ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`k`, `PRE (LENGTH out)`] mp_tac) >> simp[]
QED

Theorem dft_block_bb_well_formed:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  bb_well_formed (dft_block order bb)
Proof
  strip_tac >> drule_all dft_block_last >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  simp[bb_well_formed_def] >> rpt conj_tac
  >- gvs[bb_well_formed_def]
  >- (rpt strip_tac >> irule dft_block_unique_terminator >> simp[])
  >> rpt strip_tac >> irule dft_block_phi_prefix >> simp[] >> metis_tac[]
QED

Definition dft_block_rel_def:
  dft_block_rel a b <=>
    b.bb_label = a.bb_label /\
    LAST b.bb_instructions = LAST a.bb_instructions /\
    bb_well_formed b /\ EVERY inst_wf b.bb_instructions /\
    EVERY inst_shape_ok b.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) b.bb_instructions) /\
    FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions =
      FILTER (\i. is_pseudo i.inst_opcode) a.bb_instructions /\
    (!i. MEM i b.bb_instructions /\ ~is_pseudo i.inst_opcode ==>
         from_block a.bb_instructions i)
End

Theorem dft_block_rel_refl:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  dft_block_rel bb bb
Proof
  simp[dft_block_rel_def, from_block_def] >> metis_tac[]
QED

Theorem dft_block_rel_trans:
  dft_block_rel a b /\ dft_block_rel b c ==> dft_block_rel a c
Proof
  simp[dft_block_rel_def] >> rpt strip_tac >>
  irule from_block_trans >> qexists_tac `b.bb_instructions` >> simp[]
QED

Theorem dft_block_rel_step:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) ==>
  dft_block_rel bb (dft_block order bb)
Proof
  strip_tac >> drule_all dft_block_last >>
  disch_then (qspec_then `order` strip_assume_tac) >>
  simp[dft_block_rel_def, dft_block_phis] >> rpt conj_tac
  >- simp[dft_block_def, LET_THM]
  >- (irule dft_block_bb_well_formed >> simp[])
  >- (irule dft_block_inst_wf >> simp[])
  >- (irule dft_block_inst_shape >> simp[])
  >- (irule dft_block_distinct_ids >> simp[])
  >> rpt strip_tac >> irule dft_block_from_orig >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem dft_block_rel_schedule:
  dft_block_rel a b ==> dft_block_rel a (dft_block order b)
Proof
  strip_tac >> irule dft_block_rel_trans >> qexists_tac `b` >> simp[] >>
  irule dft_block_rel_step >> gvs[dft_block_rel_def]
QED

Theorem dft_block_rel_replace:
  LIST_REL dft_block_rel orig blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) blocks) /\
  lookup_block lbl blocks = SOME bb ==>
  LIST_REL dft_block_rel orig
    (MAP (\b. if b.bb_label = lbl then dft_block order bb else b) blocks)
Proof
  strip_tac >> simp[LIST_REL_MAP2] >> irule LIST_REL_mono >>
  qexists_tac `\a b. dft_block_rel a b /\ MEM b blocks` >>
  conj_tac
  >- (simp[] >> map_every qx_gen_tac [`a`, `b`] >> strip_tac >>
      Cases_on `b.bb_label = lbl` >> simp[] >>
      `lookup_block lbl blocks = SOME b` by
        (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
      `b = bb` by metis_tac[optionTheory.SOME_11] >>
      gvs[] >> irule dft_block_rel_schedule >> simp[]) >>
  gvs[LIST_REL_EL_EQN] >> simp[EL_MEM]
QED

Theorem dft_block_rel_labels:
  LIST_REL dft_block_rel orig blocks ==>
  MAP (\b. b.bb_label) blocks = MAP (\b. b.bb_label) orig
Proof
  qid_spec_tac `blocks` >> Induct_on `orig` >> Cases_on `blocks` >>
  simp[LIST_REL_def, dft_block_rel_def] >> metis_tac[]
QED

Theorem dft_process_one_block_rel:
  LIST_REL dft_block_rel orig st.dls_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) orig) ==>
  LIST_REL dft_block_rel orig
    (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  strip_tac >> simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  irule dft_block_rel_replace >> simp[] >>
  drule dft_block_rel_labels >> simp[]
QED

Theorem dft_loop_step_block_rel:
  !trip. LIST_REL dft_block_rel orig (FST trip).dls_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) orig) ==>
  LIST_REL dft_block_rel orig
    (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >> Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >> Cases_on `r` >> simp[] >>
  drule_all dft_process_one_block_rel >>
  disch_then (qspecl_then [`lr`, `h`, `fn`, `cfg`] mp_tac) >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem funpow_dft_block_rel:
  !n trip. LIST_REL dft_block_rel orig (FST trip).dls_blocks /\
  ALL_DISTINCT (MAP (\b. b.bb_label) orig) ==>
  LIST_REL dft_block_rel orig
    (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_block_rel >> simp[] >> first_x_assum irule >> simp[]
QED

Theorem dft_fn_block_rel:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY inst_shape_ok (fn_insts fn) ==>
  LIST_REL dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks
Proof
  strip_tac >>
  `LIST_REL dft_block_rel fn.fn_blocks fn.fn_blocks` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     `MEM (EL n fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
     irule dft_block_rel_refl >> rpt conj_tac
     >~ [`ALL_DISTINCT _`] >- (irule wf_fn_block_inst_ids_distinct >> metis_tac[])
     >~ [`bb_well_formed _`] >- (gvs[wf_function_def] >> metis_tac[])
     >~ [`EVERY inst_wf _`] >- (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
     gvs[EVERY_MEM, fn_insts_MEM] >>
     metis_tac[]) >>
  simp[dft_fn_def, LET_THM] >> pairarg_tac >> simp[] >>
  qmatch_asmsub_abbrev_tac `FUNPOW dstep fuel initial` >>
  `LIST_REL dft_block_rel fn.fn_blocks
     (FST (FUNPOW dstep fuel initial)).dls_blocks` by
    (simp[NoAsms, Abbr `dstep`, Abbr `initial`] >> irule funpow_dft_block_rel >>
     gvs[wf_function_def, fn_labels_def]) >> gvs[]
QED

Theorem dft_block_rel_source:
  dft_block_rel a b /\ MEM i b.bb_instructions ==>
  ?j. MEM j a.bb_instructions /\
      (i = j \/ (i = flip_operands j /\ is_flippable j.inst_opcode))
Proof
  strip_tac >> Cases_on `is_pseudo i.inst_opcode`
  >- (`MEM i (FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions)` by
        simp[MEM_FILTER] >>
      gvs[dft_block_rel_def] >>
      `MEM i a.bb_instructions` by metis_tac[MEM_FILTER] >>
      qexists_tac `i` >> simp[]) >>
  gvs[dft_block_rel_def] >>
  `from_block a.bb_instructions i` by metis_tac[] >>
  gvs[from_block_def] >> metis_tac[]
QED

Theorem dft_block_rel_ids:
  dft_block_rel a b ==>
  !id. MEM id (MAP (\i. i.inst_id) b.bb_instructions) ==>
       MEM id (MAP (\i. i.inst_id) a.bb_instructions)
Proof
  simp[MEM_MAP] >> rpt strip_tac >> drule_all dft_block_rel_source >>
  strip_tac >> gvs[flip_operands_inst_id] >> metis_tac[]
QED

Theorem dft_block_rel_succs:
  bb_well_formed a /\ dft_block_rel a b ==> bb_succs b = bb_succs a
Proof
  strip_tac >>
  `a.bb_instructions <> [] /\ b.bb_instructions <> [] /\
   LAST b.bb_instructions = LAST a.bb_instructions` by
    gvs[dft_block_rel_def, bb_well_formed_def] >>
  qpat_x_assum `bb_well_formed a` kall_tac >>
  qpat_x_assum `dft_block_rel a b` kall_tac >>
  simp[bb_succs_def] >>
  Cases_on `a.bb_instructions` >- gvs[] >>
  Cases_on `b.bb_instructions` >> gvs[]
QED

Theorem dft_blocks_rel_ids:
  !orig blocks. LIST_REL dft_block_rel orig blocks ==>
  !id. MEM id (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) blocks)) ==>
       MEM id (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) orig))
Proof
  Induct >> Cases_on `blocks` >> simp[LIST_REL_def] >>
  metis_tac[dft_block_rel_ids]
QED

Theorem dft_blocks_rel_distinct_ids:
  !orig blocks. LIST_REL dft_block_rel orig blocks /\
  ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) orig)) ==>
  ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions) blocks))
Proof
  Induct >> Cases_on `blocks` >> simp[LIST_REL_def, ALL_DISTINCT_APPEND] >>
  rpt strip_tac
  >- gvs[dft_block_rel_def] >>
  drule_all dft_block_rel_ids >> strip_tac >>
  drule_all dft_blocks_rel_ids >> strip_tac >> metis_tac[]
QED

Theorem dft_blocks_rel_source:
  LIST_REL dft_block_rel orig blocks /\ MEM b blocks ==>
  ?a. MEM a orig /\ dft_block_rel a b
Proof
  simp[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]
QED

Theorem dft_fn_inst_wf:
  wf_function fn /\ fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn) ==>
  fn_inst_wf (dft_fn fn)
Proof
  strip_tac >> drule_all dft_fn_block_rel >> strip_tac >>
  simp[fn_inst_wf_def] >> rpt strip_tac >>
  drule_all dft_blocks_rel_source >> strip_tac >>
  gvs[dft_block_rel_def, EVERY_MEM]
QED

Theorem dft_fn_inst_shape:
  wf_function fn /\ fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn) ==>
  EVERY inst_shape_ok (fn_insts (dft_fn fn))
Proof
  strip_tac >> drule_all dft_fn_block_rel >> strip_tac >>
  simp[EVERY_MEM, fn_insts_MEM] >> rpt strip_tac >>
  drule_all dft_blocks_rel_source >> strip_tac >>
  gvs[dft_block_rel_def, EVERY_MEM]
QED

Theorem dft_fn_wf_function:
  wf_function fn /\ fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn) ==>
  wf_function (dft_fn fn)
Proof
  strip_tac >> drule_all dft_fn_block_rel >> strip_tac >>
  drule dft_block_rel_labels >> strip_tac >>
  simp[wf_function_def] >> rpt conj_tac
  >~ [`ALL_DISTINCT _`] >- gvs[wf_function_def, fn_labels_def]
  >~ [`fn_has_entry _`] >- (gvs[fn_has_entry_def, wf_function_def] >>
                              metis_tac[MAP_EQ_NIL])
  >~ [`!bb. MEM bb _ ==> bb_well_formed bb`]
  >- (rpt strip_tac >> drule_all dft_blocks_rel_source >> strip_tac >>
      gvs[dft_block_rel_def])
  >~ [`fn_inst_ids_distinct _`]
  >- (simp[fn_inst_ids_distinct_def] >> irule dft_blocks_rel_distinct_ids >>
      qexists_tac `fn.fn_blocks` >> gvs[wf_function_def, fn_inst_ids_distinct_def]) >>
  simp[fn_succs_closed_def] >> rpt strip_tac >>
  drule_all dft_blocks_rel_source >> strip_tac >>
  `bb_succs bb = bb_succs a` by
    (irule dft_block_rel_succs >> gvs[wf_function_def] >> metis_tac[]) >>
  gvs[wf_function_def, fn_succs_closed_def, fn_labels_def] >> metis_tac[]
QED

Theorem dft_fn_ir_inst_ids_subset:
  wf_function fn /\ fn_inst_wf fn /\ EVERY inst_shape_ok (fn_insts fn) ==>
  !id. MEM id (fn_ir_inst_ids (dft_fn fn)) ==> MEM id (fn_ir_inst_ids fn)
Proof
  strip_tac >> drule_all dft_fn_block_rel >> strip_tac >>
  drule dft_blocks_rel_ids >>
  simp[fn_ir_inst_ids_def, GSYM (lambdify block_ir_inst_ids_def)]
QED
