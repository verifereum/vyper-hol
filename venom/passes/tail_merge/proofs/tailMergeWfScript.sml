(*
 * Tail Merge Pass — ssa_form and wf_function preservation
 *
 * The pass rewrites label operands of terminators and PHIs, then drops the
 * merged blocks; instruction outputs and ids are unchanged, so their
 * projections in the transformed function are sublists of the originals.
 *)

Theory tailMergeWf
Ancestors
  tailMergeMap tailMergeHelpers tailMergeDefs cfgTransformProps cfgTransform
  venomInst venomWf

(* Outputs of the kept, substituted blocks: distinct, and among the
   original outputs *)
Theorem outputs_filter_subst[local]:
  !P m bbs.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (FILTER P (MAP (subst_block_labels_block m) bbs))))) /\
    !x. MEM x (FLAT (MAP (\i. i.inst_outputs)
          (fn_insts_blocks (FILTER P (MAP (subst_block_labels_block m) bbs))))) ==>
        MEM x (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
Proof
  gen_tac >> gen_tac >> Induct >>
  simp[fn_insts_blocks_def] >> rpt gen_tac >> strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  IF_CASES_TAC >>
  gvs[fn_insts_blocks_def, listTheory.ALL_DISTINCT_APPEND, subst_block_labels_block_def,
      listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  metis_tac[]
QED

Theorem tail_merge_fn_ssa_form:
  !func. ssa_form func ==> ssa_form (tail_merge_fn func)
Proof
  rw[tail_merge_fn_def] >> Cases_on `fn_entry_label func` >> simp[] >>
  rw[] >> gvs[ssa_form_def, fn_insts_def, subst_block_labels_fn_def] >>
  metis_tac[outputs_filter_subst]
QED

Theorem operand_labels_subst[local]:
  !ops m s.
    MEM s (MAP THE (FILTER IS_SOME
      (MAP get_label (MAP (subst_label_map_op m) ops)))) <=>
    ?l. MEM l (MAP THE (FILTER IS_SOME (MAP get_label ops))) /\
        s = (case ALOOKUP m l of NONE => l | SOME k => k)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[subst_label_map_op_def, venomStateTheory.get_label_def] >>
  Cases_on `ALOOKUP m s'` >>
  simp[venomStateTheory.get_label_def,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem get_successors_subst_block_labels[local]:
  !m inst s.
    MEM s (get_successors (subst_block_labels_inst m inst)) <=>
    ?l. MEM l (get_successors inst) /\
        s = (case ALOOKUP m l of NONE => l | SOME k => k)
Proof
  rpt gen_tac >> Cases_on `is_terminator inst.inst_opcode` >>
  simp[get_successors_def, subst_block_labels_inst_def,
       is_block_label_opcode_def, subst_label_map_inst_def,
       operand_labels_subst]
QED

Theorem bb_succs_subst_block_labels[local]:
  !m bb s.
    MEM s (bb_succs (subst_block_labels_block m bb)) <=>
    ?l. MEM l (bb_succs bb) /\
        s = (case ALOOKUP m l of NONE => l | SOME k => k)
Proof
  rpt gen_tac >> Cases_on `bb.bb_instructions` >>
  simp[bb_succs_def, subst_block_labels_block_def,
       listTheory.LAST_MAP, get_successors_subst_block_labels] >>
  qspecl_then [`h::t`, `subst_block_labels_inst m`] mp_tac
    listTheory.LAST_MAP >>
  (impl_tac >- simp[]) >>
  pure_rewrite_tac [listTheory.MAP] >>
  disch_then SUBST1_TAC >> simp[get_successors_subst_block_labels]
QED

Theorem labels_filter_subst[local]:
  !bbs m removed.
    MAP (\bb. bb.bb_label)
      (FILTER (\bb. ~MEM bb.bb_label removed)
        (MAP (subst_block_labels_block m) bbs)) =
    MAP (\bb. bb.bb_label) (FILTER (\bb. ~MEM bb.bb_label removed) bbs)
Proof
  Induct >> simp[] >> rpt gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem labels_filter_distinct[local]:
  !bbs removed.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP (\bb. bb.bb_label)
      (FILTER (\bb. ~MEM bb.bb_label removed) bbs))
Proof
  Induct >> simp[] >> rpt strip_tac >> IF_CASES_TAC >>
  gvs[listTheory.MEM_MAP, listTheory.MEM_FILTER] >> metis_tac[]
QED

Theorem ids_filter_subst[local]:
  !P m bbs.
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)) ==>
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (FILTER P (MAP (subst_block_labels_block m) bbs)))) /\
    !x. MEM x (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (FILTER P (MAP (subst_block_labels_block m) bbs)))) ==>
    MEM x (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs))
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[listTheory.ALL_DISTINCT_APPEND] >>
  IF_CASES_TAC >>
  gvs[subst_block_labels_block_def, subst_block_labels_inst_shape, listTheory.MAP_MAP_o,
      combinTheory.o_DEF, listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem wf_blocks_filter_subst[local]:
  !bbs m P. EVERY bb_well_formed bbs ==>
    EVERY bb_well_formed (FILTER P (MAP (subst_block_labels_block m) bbs))
Proof
  simp[listTheory.EVERY_MEM, listTheory.MEM_FILTER, listTheory.MEM_MAP] >>
  metis_tac[bb_well_formed_subst_block_labels]
QED

Theorem entry_filter_subst_nonempty[local]:
  !func entry removed m.
    fn_entry_label func = SOME entry /\ ~MEM entry removed ==>
    FILTER (\bb. ~MEM bb.bb_label removed)
      (MAP (subst_block_labels_block m) func.fn_blocks) <> []
Proof
  rpt gen_tac >> Cases_on `func.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def] >> rpt strip_tac >> simp[]
QED

Theorem succs_closed_merge_filter[local]:
  !func entry.
    ALL_DISTINCT (fn_labels func) /\ fn_succs_closed func ==>
    let m = compute_merge_map (block_sigs func entry func.fn_blocks) [] in
    fn_succs_closed (func with fn_blocks :=
      FILTER (\bb. ~MEM bb.bb_label (MAP FST m))
        (MAP (subst_block_labels_block m) func.fn_blocks))
Proof
  rpt gen_tac >> strip_tac >>
  simp[fn_succs_closed_def, fn_labels_def, labels_filter_subst,
       listTheory.MEM_FILTER, listTheory.MEM_MAP] >>
  rpt strip_tac >> gvs[bb_succs_subst_block_labels] >>
  `MEM l (fn_labels func)` by metis_tac[fn_succs_closed_def] >>
  drule_all compute_merge_map_image_survives >>
  disch_then (qspec_then `entry` mp_tac) >>
  simp[listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  strip_tac >>
  qexists_tac `subst_block_labels_block
    (compute_merge_map (block_sigs func entry func.fn_blocks) []) bb` >>
  simp[] >> metis_tac[]
QED

Theorem tail_merge_fn_wf_function:
  !func. wf_function func ==> wf_function (tail_merge_fn func)
Proof
  gen_tac >> strip_tac >> rw[tail_merge_fn_def] >>
  Cases_on `fn_entry_label func` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[subst_block_labels_fn_def] >>
  qmatch_goalsub_abbrev_tac `FILTER P (MAP (subst_block_labels_block m) _)` >>
  `fn_succs_closed (func with fn_blocks :=
      FILTER P (MAP (subst_block_labels_block m) func.fn_blocks))` by
    (simp[Abbr `P`, Abbr `m`] >>
     gvs[wf_function_def] >> drule_all succs_closed_merge_filter >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  gvs[wf_function_def] >>
  simp[fn_labels_def, Abbr `P`, labels_filter_subst] >>
  rpt conj_tac
  >- (irule labels_filter_distinct >> gvs[fn_labels_def])
  >- (simp[fn_has_entry_def] >> irule entry_filter_subst_nonempty >>
      qexists_tac `x` >> simp[Abbr `m`, compute_merge_map_entry_survives])
  >- (mp_tac wf_blocks_filter_subst >>
      simp[listTheory.EVERY_MEM] >> metis_tac[])
  >> gvs[fn_inst_ids_distinct_def] >> metis_tac[ids_filter_subst]
QED
