Theory makeSsaCurrentFiniteHistory
Ancestors makeSsaCurrentFiniteDemandProbe makeSsaCurrentPreorderHistory
  makeSsaCurrentTreeTrace makeSsaCurrentHistoryProbe makeSsaCurrentSimDefs
  makeSsaCurrentDefs list rich_list

Theorem current_result_preorder_trace:
  ALL_DISTINCT (dom_tree_labels tree) /\
  current_unvisited_annotations A [] bbs /\
  (!l. MEM l (dom_tree_labels tree) ==> IS_SOME (lookup_block l bbs)) /\
  rename_current_blocks s rs bbs sm tree = (ctrs',s',bbs') ==>
  ?visited' events.
    current_tree_trace A sm tree s rs bbs [] E [] ctrs' s' bbs'
      (current_preorder_history A (dom_tree_labels tree) bbs') visited' events
Proof
  strip_tac >>
  `?H' visited' events.
    current_tree_trace A sm tree s rs bbs [] E [] ctrs' s' bbs' H' visited' events` by
    (irule current_tree_trace_for_result >> simp[]) >>
  drule_all current_tree_trace_preorder_history >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Definition current_finite_annotation_map_def:
  current_finite_annotation_map fn =
    current_annotation_map (FST (history_probe_insert fn)) (current_finite_annotations fn)
End

Definition current_finite_initial_rename_def:
  current_finite_initial_rename fn =
    init_current_rename_state (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
End

Definition current_finite_rename_result_def:
  current_finite_rename_result fn = rename_current_blocks
    (SND (history_probe_insert fn)) (current_finite_initial_rename fn)
    (FST (history_probe_insert fn)) (current_succ_map fn) (current_dom_tree fn)
End

Theorem current_finite_rename_result_blocks:
  SND (SND (current_finite_rename_result fn)) = history_probe_rename fn
Proof
  simp[current_finite_rename_result_def, current_finite_initial_rename_def,
       history_probe_rename_def]
QED

Theorem current_finite_history_preorder:
  current_preorder_history (current_finite_annotation_map current_probe_loop)
    (dom_tree_labels (current_dom_tree current_probe_loop))
    (history_probe_rename current_probe_loop) = current_finite_history current_probe_loop /\
  current_preorder_history (current_finite_annotation_map history_probe_backedges)
    (dom_tree_labels (current_dom_tree history_probe_backedges))
    (history_probe_rename history_probe_backedges) = current_finite_history history_probe_backedges
Proof
  conj_tac >- EVAL_TAC >>
  CONV_TAC (LHS_CONV EVAL) >> CONV_TAC (RHS_CONV EVAL) >> REFL_TAC
QED

Theorem current_finite_history_annotations:
  current_unvisited_annotations (current_finite_annotation_map current_probe_loop) []
    (FST (history_probe_insert current_probe_loop)) /\
  current_unvisited_annotations (current_finite_annotation_map history_probe_backedges) []
    (FST (history_probe_insert history_probe_backedges))
Proof
  conj_tac >> EVAL_TAC >> rpt gen_tac >> rpt IF_CASES_TAC >> gvs[]
QED

Theorem current_finite_history_coverage:
  (!l. MEM l (dom_tree_labels (current_dom_tree current_probe_loop)) ==>
    IS_SOME (lookup_block l (FST (history_probe_insert current_probe_loop)))) /\
  (!l. MEM l (dom_tree_labels (current_dom_tree history_probe_backedges)) ==>
    IS_SOME (lookup_block l (FST (history_probe_insert history_probe_backedges))))
Proof
  conj_tac >> EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem current_block_provenance_annotations[local]:
  current_block_provenance fn old new anns ==>
  anns = current_block_annotations old
    (TAKE (LENGTH new.bb_instructions - LENGTH old.bb_instructions) new.bb_instructions)
Proof
  simp[makeSsaCurrentCertificateTheory.current_block_provenance_def] >>
  rpt strip_tac >> gvs[] >> simp[TAKE_LENGTH_APPEND]
QED

Theorem current_block_provenance_canonical_list[local]:
  !olds news.
  LIST_REL (\old new. ?anns. current_block_provenance fn old new anns) olds news ==>
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (olds,news))
    (MAP (\(old,new). current_block_annotations old
      (TAKE (LENGTH new.bb_instructions - LENGTH old.bb_instructions)
        new.bb_instructions)) (ZIP (olds,news)))
Proof
  Induct >> Cases_on `news` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  drule current_block_provenance_annotations >> strip_tac >> gvs[]
QED

Theorem current_history_insert_provenance[local]:
  !fn. LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (fn.fn_blocks,FST (history_probe_insert fn)))
    (MAP (\(old,new). current_block_annotations old
      (TAKE (LENGTH new.bb_instructions - LENGTH old.bb_instructions)
        new.bb_instructions)) (ZIP (fn.fn_blocks,FST (history_probe_insert fn))))
Proof
  gen_tac >> irule current_block_provenance_canonical_list >>
  irule makeSsaCurrentCertificateTheory.current_actual_block_provenance >>
  qexistsl [`history_probe_supply`, `SND (history_probe_insert fn)`] >>
  simp[GSYM history_probe_insert_def]
QED

Theorem current_finite_canonical_annotations[local]:
  MAP (\(old,new). current_block_annotations old
      (TAKE (LENGTH new.bb_instructions - LENGTH old.bb_instructions)
        new.bb_instructions))
    (ZIP (current_probe_loop.fn_blocks,FST (history_probe_insert current_probe_loop))) =
    current_finite_annotations current_probe_loop /\
  MAP (\(old,new). current_block_annotations old
      (TAKE (LENGTH new.bb_instructions - LENGTH old.bb_instructions)
        new.bb_instructions))
    (ZIP (history_probe_backedges.fn_blocks,FST (history_probe_insert history_probe_backedges))) =
    current_finite_annotations history_probe_backedges
Proof
  conj_tac >> CONV_TAC (LHS_CONV EVAL) >> CONV_TAC (RHS_CONV EVAL) >> REFL_TAC
QED

Theorem current_finite_history_provenance:
  LIST_REL (\pair anns. current_block_provenance current_probe_loop
      (FST pair) (SND pair) anns)
    (ZIP (current_probe_loop.fn_blocks,FST (history_probe_insert current_probe_loop)))
    (current_finite_annotations current_probe_loop) /\
  LIST_REL (\pair anns. current_block_provenance history_probe_backedges
      (FST pair) (SND pair) anns)
    (ZIP (history_probe_backedges.fn_blocks,FST (history_probe_insert history_probe_backedges)))
    (current_finite_annotations history_probe_backedges)
Proof
  conj_tac
  >- (qspec_then `current_probe_loop` mp_tac current_history_insert_provenance >>
      simp[current_finite_canonical_annotations]) >>
  qspec_then `history_probe_backedges` mp_tac current_history_insert_provenance >>
  simp[current_finite_canonical_annotations]
QED

Theorem current_finite_history_trace:
  !fn. (fn = current_probe_loop \/ fn = history_probe_backedges) ==>
  ?visited' events.
    current_tree_trace (current_finite_annotation_map fn) (current_succ_map fn)
      (current_dom_tree fn) (SND (history_probe_insert fn))
      (current_finite_initial_rename fn) (FST (history_probe_insert fn)) [] E []
      (FST (current_finite_rename_result fn))
      (FST (SND (current_finite_rename_result fn))) (history_probe_rename fn)
      (current_finite_history fn) visited' events
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    (gvs[] >> EVAL_TAC) >>
  `current_unvisited_annotations (current_finite_annotation_map fn) []
    (FST (history_probe_insert fn))` by
    (gvs[] >> simp[current_finite_history_annotations]) >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==>
    IS_SOME (lookup_block l (FST (history_probe_insert fn)))` by
    (gvs[] >> simp[current_finite_history_coverage]) >>
  `current_preorder_history (current_finite_annotation_map fn)
    (dom_tree_labels (current_dom_tree fn)) (history_probe_rename fn) =
    current_finite_history fn` by
    (gvs[] >> simp[current_finite_history_preorder]) >>
  qpat_x_assum `current_preorder_history _ _ _ = _`
    (fn th => rewrite_tac[GSYM th]) >>
  irule current_result_preorder_trace >> simp[] >>
  simp[GSYM current_finite_rename_result_def,
       GSYM current_finite_rename_result_blocks]
QED

(* The preorder swaps S and D relative to fn_blocks; S contributes no allocation. *)
Theorem current_finite_backedges_S_delta:
  current_preorder_history (current_finite_annotation_map history_probe_backedges)
    ["S"] (history_probe_rename history_probe_backedges) = []
Proof
  EVAL_TAC
QED
