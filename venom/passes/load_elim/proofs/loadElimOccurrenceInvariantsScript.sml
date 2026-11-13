Theory loadElimOccurrenceInvariants
Ancestors
  loadElimHomogeneousCurrentness loadElimSentinelHelpers
  codegenReadyCompute cfgAnalysisProps instIdxIndep pred_set list
  venomExecProofs venomMemDefs memLocDefs venomState basePtrDefs
  dfgCorrectnessProof memoryCopyElisionSound loadElimSingletonSuffix
  loadElimOccurrence loadElimSingletonCurrentness

Theorem le_ptr_matches_inst_idx[local,simp]:
  ptr_matches_var p v (s with vs_inst_idx := n) = ptr_matches_var p v s
Proof
  Cases_on `p` >> rename1 `Ptr a off` >>
  Cases_on `off` >> Cases_on `a` >> simp[ptr_matches_var_def, lookup_var_def]
QED

Theorem le_step_invariants_inst_idx[simp]:
  le_step_invariants bp dfg fn (s with vs_inst_idx := n) =
  le_step_invariants bp dfg fn s
Proof
  simp[le_step_invariants_def, dfg_assigns_sound_def,
       lookup_var_def, eval_op_inst_idx, bp_ptr_sound_def,
       ptr_matches_var_def, allocas_non_overlapping_def,
       allocas_in_word_def, bp_ptrs_bounded_def, memloc_within_alloca_def]
QED

Theorem le_step_invariants_phi:
  (!v. bp_get_ptrs bp v = []) /\
  le_step_invariants bp dfg fn u /\
  eval_phis u insts = OK t /\ dfg_assigns_sound dfg t ==>
  le_step_invariants bp dfg fn t
Proof
  strip_tac >> drule eval_phis_preserves_alloca_fields >> strip_tac >>
  gvs[le_step_invariants_def, bp_ptr_sound_def,
      allocas_non_overlapping_def, allocas_in_word_def,
      bp_ptrs_bounded_def, memloc_within_alloca_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem le_step_invariants_step:
  le_step_preserves bp dfg fn /\ le_step_invariants bp dfg fn u /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\ inst_wf inst /\
  step_inst fuel C inst u = OK t ==>
  le_step_invariants bp dfg fn t
Proof
  simp[le_step_preserves_def] >> metis_tac[le_step_invariants_inst_idx]
QED

Theorem le_occ_phi_dfs:
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\ MEM (PhiOcc bb u t) es ==>
  MEM bb fn.fn_blocks /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> drule_all le_occ_phi_static >> strip_tac >> simp[] >>
  drule fn_reachable_cfg_analyze >> strip_tac >>
  drule cfg_analyze_reachable_sets >> simp[EXTENSION] >> metis_tac[]
QED

Theorem le_occ_prefix_invariants:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!v. bp_get_ptrs bp v = []) /\
  le_step_invariants bp (dfg_build_function fn) fn s0 /\
  le_step_preserves bp (dfg_build_function fn) fn /\
  (!bb u t. MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    eval_phis u bb.bb_instructions = OK t /\
    dfg_assigns_sound (dfg_build_function fn) u ==>
    dfg_assigns_sound (dfg_build_function fn) t) ==>
  le_step_invariants bp (dfg_build_function fn) fn s /\
  EVERY (\q. le_step_invariants bp (dfg_build_function fn) fn (le_occ_pre q) /\
             le_step_invariants bp (dfg_build_function fn) fn (le_occ_post q)) es
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- suspend "start"
  >- suspend "next"
  >> suspend "block"
QED

Resume le_occ_prefix_invariants[start]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  `le_occ_prefix C fn s0 [PhiOcc bb s0 p] i
     (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule (cj 1 le_occ_prefix_rules) >> simp[]) >>
  `MEM bb fn.fn_blocks /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (irule le_occ_phi_dfs >> metis_tac[MEM]) >>
  `dfg_assigns_sound (dfg_build_function fn) p` by
    (fs[le_step_invariants_def] >> metis_tac[]) >>
  `le_step_invariants bp (dfg_build_function fn) fn p` by
    (irule le_step_invariants_phi >> metis_tac[]) >>
  simp[le_occ_pre_def, le_occ_post_def]
QED
Resume le_occ_prefix_invariants[next]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> le_step_invariants _ _ _ s /\ _`
    (fn th => mp_tac th) >> impl_tac >- metis_tac[] >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by metis_tac[EL_MEM] >>
  `inst_wf i` by metis_tac[fn_inst_wf_every_bb, EVERY_MEM] >>
  `le_step_invariants bp (dfg_build_function fn) fn u` by
    (irule le_step_invariants_step >> metis_tac[]) >>
  simp[EVERY_APPEND, le_occ_pre_def, le_occ_post_def]
QED
Resume le_occ_prefix_invariants[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> le_step_invariants _ _ _ s /\ _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM i bb.bb_instructions` by metis_tac[EL_MEM] >>
  `inst_wf i` by metis_tac[fn_inst_wf_every_bb, EVERY_MEM] >>
  `le_step_invariants bp (dfg_build_function fn) fn u` by
    (irule le_step_invariants_step >> metis_tac[]) >>
  `le_occ_prefix C fn s0
     (es ++ [StepOcc bb s.vs_inst_idx k s u; PhiOcc next u p]) i'
     (p with vs_inst_idx := phi_prefix_length next.bb_instructions)` by
    (irule (cj 3 le_occ_prefix_rules) >> metis_tac[]) >>
  `MEM next fn.fn_blocks /\ MEM next.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (irule le_occ_phi_dfs >> metis_tac[MEM_APPEND, MEM]) >>
  `dfg_assigns_sound (dfg_build_function fn) p` by
    (fs[le_step_invariants_def] >> metis_tac[]) >>
  `le_step_invariants bp (dfg_build_function fn) fn p` by
    (irule le_step_invariants_phi >> metis_tac[]) >>
  simp[EVERY_APPEND, le_occ_pre_def, le_occ_post_def]
QED
Finalise le_occ_prefix_invariants

Theorem le_occ_invariants_step_dfg:
  EVERY (\q. le_step_invariants bp dfg fn (le_occ_pre q) /\
              le_step_invariants bp dfg fn (le_occ_post q)) es ==>
  !bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
    dfg_assigns_sound dfg u /\ dfg_assigns_sound dfg t
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[le_occ_pre_def, le_occ_post_def,
                             le_step_invariants_def]
QED

Theorem le_occ_prefix_frozen_invariants:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!v. bp_get_ptrs bp v = []) /\
  dfg_assigns_sound (dfg_build_function fn) s0 /\
  bp_ptr_sound bp s0 /\ alloca_inv s0 /\ allocas_in_word s0 /\
  bp_ptrs_bounded bp fn s0 /\
  le_step_preserves bp (dfg_build_function fn) fn /\
  (!bb u t. MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    eval_phis u bb.bb_instructions = OK t /\
    dfg_assigns_sound (dfg_build_function fn) u ==>
    dfg_assigns_sound (dfg_build_function fn) t) ==>
  le_step_invariants bp (dfg_build_function fn) fn s /\
  EVERY (\q. le_step_invariants bp (dfg_build_function fn) fn (le_occ_pre q) /\
             le_step_invariants bp (dfg_build_function fn) fn (le_occ_post q)) es
Proof
  strip_tac >> drule le_occ_prefix_invariants >>
  simp[le_step_invariants_def, alloca_inv_def] >> metis_tac[alloca_inv_def]
QED

Theorem le_occ_prefix_frozen_dfg:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!v. bp_get_ptrs bp v = []) /\
  dfg_assigns_sound (dfg_build_function fn) s0 /\
  bp_ptr_sound bp s0 /\ alloca_inv s0 /\ allocas_in_word s0 /\
  bp_ptrs_bounded bp fn s0 /\
  le_step_preserves bp (dfg_build_function fn) fn /\
  (!bb u t. MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    eval_phis u bb.bb_instructions = OK t /\
    dfg_assigns_sound (dfg_build_function fn) u ==>
    dfg_assigns_sound (dfg_build_function fn) t) ==>
  dfg_assigns_sound (dfg_build_function fn) s /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
    dfg_assigns_sound (dfg_build_function fn) u /\
    dfg_assigns_sound (dfg_build_function fn) t)
Proof
  strip_tac >> drule_all le_occ_prefix_frozen_invariants >> strip_tac >>
  conj_tac >- fs[le_step_invariants_def] >>
  drule le_occ_invariants_step_dfg >> simp[]
QED
