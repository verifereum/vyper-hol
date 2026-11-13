Theory dftGasInvSourceLineage
Ancestors
  dftGasInvStackLineage dftGasInvForwardParents dftDefs dftStructural
  list rich_list arithmetic venomInst venomWf venomEffects passSharedDefs
  dftRunRel dftIdempotent dftCorrectness dftWf dftTopoSort contextCodegenRel

Definition inv_line_source_rep_def:
  inv_line_source_rep bi order eda om do_flip entries st <=>
    ?frames roots.
      st.ds_stack = inv_line_flat (inv_line_emit bi order eda om do_flip) frames roots /\
      inv_line_ok (inv_line_children bi order eda om) entries frames roots /\
      EVERY (\frame. MEM (FST frame) bi /\
        ~is_pseudo (FST frame).inst_opcode) frames
End

Theorem inv_line_link_mem:
  inv_line_link whole p rs ==> MEM p whole
Proof
  simp[inv_line_link_def] >> rpt strip_tac >> simp[]
QED

Theorem inv_line_suffix_mem:
  inv_line_suffix whole (h::rs) ==> MEM h whole
Proof
  simp[inv_line_suffix_def] >> rpt strip_tac >> simp[]
QED

Theorem inv_line_source_rep_step:
  (!p. MEM p entries ==> MEM p bi) /\
  (!p h. MEM p bi /\ ~is_pseudo p.inst_opcode /\
    MEM h (inv_line_children bi order eda om p) ==> MEM h bi) /\
  inv_line_source_rep bi order eda om do_flip entries st ==>
  inv_line_source_rep bi order eda om do_flip entries
    (dfs_step bi order eda om do_flip st)
Proof
  simp[inv_line_source_rep_def] >> rpt strip_tac >>
  Cases_on `frames`
  >- (Cases_on `roots`
      >- (qexistsl [`[]`, `[]`] >> gvs[inv_line_flat_def, dfs_step_def]) >>
      rename1 `h::rs` >>
      `MEM h bi` by
        (gvs[inv_line_ok_def] >> metis_tac[inv_line_suffix_mem]) >>
      `st.ds_stack = DfsProcess h :: MAP DfsProcess rs` by
        gvs[inv_line_flat_def] >>
      drule inv_line_process_stack >> strip_tac >>
      Cases_on `MEM h.inst_id st.ds_visited \/ is_pseudo h.inst_opcode`
      >- (qexistsl [`[]`, `rs`] >>
          gvs[inv_line_flat_def, inv_line_ok_def] >>
          metis_tac[inv_line_suffix_drop]) >>
      qexistsl [`[(h,inv_line_children bi order eda om h)]`, `rs`] >>
      simp[inv_line_flat_def] >>
      conj_tac >- (irule inv_line_root_push >> gvs[inv_line_ok_def]) >>
      gvs[]) >>
  rename1 `frame::outer` >> Cases_on `frame` >>
  rename1 `(p,pending)::outer` >> Cases_on `pending`
  >- (qexistsl [`outer`, `roots`] >>
      gvs[inv_line_flat_def, dfs_step_def, inv_line_ok_def]) >>
  rename1 `(p,h::rs)::outer` >>
  `MEM h bi` by
    (gvs[inv_line_ok_def] >> metis_tac[inv_line_suffix_mem]) >>
  `st.ds_stack = DfsProcess h ::
      inv_line_flat (inv_line_emit bi order eda om do_flip) ((p,rs)::outer) roots` by
    gvs[inv_line_flat_def] >>
  drule inv_line_process_stack >> strip_tac >>
  Cases_on `MEM h.inst_id st.ds_visited \/ is_pseudo h.inst_opcode`
  >- (qexistsl [`(p,rs)::outer`, `roots`] >> simp[] >>
      gvs[] >> metis_tac[inv_line_ok_advance]) >>
  qexistsl [`(h,inv_line_children bi order eda om h)::(p,rs)::outer`, `roots`] >>
  simp[inv_line_flat_def] >> gvs[] >> metis_tac[inv_line_ok_push]
QED

Theorem inv_line_source_initialized:
  eda_wf eda bi /\ (!p. MEM p entries ==> MEM p bi) ==>
  !ticks. inv_line_source_rep bi order eda om do_flip entries
    (inv_line_state bi order eda om do_flip entries ticks)
Proof
  strip_tac >> Induct
  >- (simp[inv_line_state_def, inv_line_source_rep_def] >>
      qexistsl [`[]`, `entries`] >>
      simp[inv_line_flat_def, inv_line_ok_def, inv_line_suffix_def]) >>
  simp[inv_line_state_def, FUNPOW_SUC] >>
  irule inv_line_source_rep_step >>
  gvs[inv_line_state_def, inv_line_children_def, sort_children_mem] >>
  metis_tac[inst_all_deps_mem]
QED

Theorem inv_line_source_initialized_emit:
  eda_wf eda bi /\ (!p. MEM p entries ==> MEM p bi) /\
  (inv_line_state bi order eda om do_flip entries ticks).ds_stack =
    DfsEmit c :: rest ==>
  ?p outer roots.
    MEM p bi /\ ~is_pseudo p.inst_opcode /\
    inv_line_emit bi order eda om do_flip p = c /\
    rest = inv_line_flat (inv_line_emit bi order eda om do_flip) outer roots /\
    (case outer of [] => inv_line_link entries p roots
     | (q,qs)::more => inv_line_link (inv_line_children bi order eda om q) p qs) /\
    inv_line_ok (inv_line_children bi order eda om) entries outer roots /\
    EVERY (\frame. MEM (FST frame) bi /\
      ~is_pseudo (FST frame).inst_opcode) outer
Proof
  strip_tac >> drule_all inv_line_source_initialized >>
  disch_then (qspecl_then [`order`, `om`, `do_flip`, `ticks`] mp_tac) >>
  simp[inv_line_source_rep_def] >> rpt strip_tac >>
  qpat_x_assum `DfsEmit _ :: _ = _` (assume_tac o SYM) >>
  drule inv_line_flat_emit_head >> strip_tac >>
  gvs[inv_line_ok_def] >> metis_tac[]
QED

Theorem inv_line_emit_copy_original[local]:
  inv_line_emit bi order eda om do_flip p = copy /\
  copy.inst_opcode = RETURNDATACOPY ==> p = copy
Proof
  simp[inv_line_emit_def] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  Cases_on `p.inst_opcode` >>
  gvs[is_flippable_def, is_commutative_def, is_comparator_def] >>
  namedCases_on `p.inst_operands` ["", "a rest"] >> gvs[flip_operands_def] >>
  namedCases_on `rest` ["", "b more"] >> gvs[flip_operands_def] >>
  Cases_on `more` >>
  gvs[flip_operands_def, is_comparator_def, flip_comparison_opcode_def]
QED

Theorem inv_forward_initialized_frame:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev /\
  st = inv_line_state bb.bb_instructions [] (dft_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions []) T
    (entry_instructions bb.bb_instructions [] (dft_eda bb.bb_instructions)) ticks /\
  st.ds_stack = DfsEmit copy :: rest ==>
  ?pending tail.
    rest = MAP DfsProcess pending ++ [DfsEmit rev] ++ tail /\
    inv_line_link (inv_line_children bb.bb_instructions []
      (dft_eda bb.bb_instructions) (build_offspring_map bb.bb_instructions []) rev)
      copy pending
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions)` by
    (irule bb_inst_ids_distinct >> gvs[dft_fn_rel_def] >> metis_tac[]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `bb_well_formed bb /\ non_pseudo_defs_before_uses bb.bb_instructions` by
    (conj_tac
     >- (gvs[dft_fn_rel_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     simp[non_pseudo_defs_before_uses_def] >>
     irule wf_ssa_defs_before_uses >> gvs[dft_fn_rel_def] >> metis_tac[]) >>
  `copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT` by
    gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  `eda_wf (dft_eda bb.bb_instructions) bb.bb_instructions` by
    metis_tac[dft_eda_wf] >>
  `!p. MEM p (entry_instructions bb.bb_instructions []
      (dft_eda bb.bb_instructions)) ==> MEM p bb.bb_instructions` by
    simp[entry_instructions_def, MEM_FILTER] >>
  qpat_x_assum `st = _` SUBST_ALL_TAC >>
  drule_all inv_line_source_initialized_emit >> strip_tac >>
  `p = copy` by metis_tac[inv_line_emit_copy_original] >>
  gvs[] >>
  Cases_on `outer`
  >- (gvs[] >> drule inv_line_link_mem >>
      metis_tac[inv_forward_copy_not_entry]) >>
  rename1 `frame::more` >> Cases_on `frame` >> rename1 `(parent,pending)::more` >>
  gvs[] >>
  `MEM copy (inst_all_deps bb.bb_instructions []
      (dft_eda bb.bb_instructions) parent)` by
    (drule inv_line_link_mem >> simp[inv_line_children_def, sort_children_mem]) >>
  `parent = rev` by metis_tac[inv_forward_copy_parent] >>
  gvs[inv_line_flat_def, inv_line_emit_def, is_flippable_def,
      is_commutative_def, is_comparator_def] >>
  metis_tac[]
QED
