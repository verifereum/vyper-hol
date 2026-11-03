(* Exact-state transport for the operand-flip normalization stage. *)
Theory dftFrameFlipSim
Ancestors
  dftFrameNormalize dftFramePrefix dftFrameFacts dftFrameSwap dftSsaPreserve dftFrameLocal
  o1PassLift venomExecSemantics venomInst venomWf contextCodegenRel
  dftDefs dftCorrectness list rich_list option unitShapeDefs ctxLookupAgreeHelpers

Theorem dft_flip_inst_phi:
  dft_flip_inst i j ==> (j.inst_opcode = PHI <=> i.inst_opcode = PHI) /\
    (i.inst_opcode = PHI ==> j = i)
Proof
  rw[dft_flip_inst_def] >> metis_tac[flip_operands_phi_test, ssa_flippable_classes]
QED

Theorem dft_flip_list_entry:
  !xs ys. LIST_REL dft_flip_inst xs ys ==>
    eval_phis s xs = eval_phis s ys /\
    phi_prefix_length xs = phi_prefix_length ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  `eval_phis s xs = eval_phis s t /\
   phi_prefix_length xs = phi_prefix_length t` by metis_tac[] >>
  `h'.inst_opcode = PHI <=> h.inst_opcode = PHI` by metis_tac[dft_flip_inst_phi] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`h' = h` by metis_tac[dft_flip_inst_phi] >>
      simp[eval_phis_def, phi_prefix_length_def]) >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem dft_flip_blocks_lookup:
  !xs ys. LIST_REL dft_flip_block xs ys ==>
    OPTREL dft_flip_block (lookup_block lbl xs) (lookup_block lbl ys)
Proof
  Induct >> Cases_on `ys` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.bb_label = h.bb_label` by fs[dft_flip_block_def] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def]
QED

Theorem dft_flip_fn_entry:
  dft_flip_fn f g ==> (enters_block g v e <=> enters_block f v e)
Proof
  strip_tac >> `OPTREL dft_flip_block
    (lookup_block v.vs_current_bb f.fn_blocks)
    (lookup_block v.vs_current_bb g.fn_blocks)` by
    metis_tac[dft_flip_fn_def, dft_flip_blocks_lookup] >>
  Cases_on `lookup_block v.vs_current_bb f.fn_blocks` >>
  Cases_on `lookup_block v.vs_current_bb g.fn_blocks` >>
  gvs[enters_block_def, dft_flip_block_def] >>
  metis_tac[dft_flip_list_entry]
QED

Theorem dft_flip_fn_active:
  dft_flip_fn f g /\ active_inst g j t ==>
    ?i. active_inst f i t /\ dft_flip_inst i j
Proof
  simp[dft_flip_fn_def, active_inst_def] >> strip_tac >>
  `?x. MEM x f.fn_blocks /\ dft_flip_block x bb` by
    (fs[MEM_EL, LIST_REL_EL_EQN] >> metis_tac[]) >>
  fs[dft_flip_block_def] >>
  `t.vs_inst_idx < LENGTH x.bb_instructions` by metis_tac[LIST_REL_LENGTH] >>
  qexists_tac `EL t.vs_inst_idx x.bb_instructions` >>
  conj_tac
  >- (qexists_tac `x` >> simp[] >> metis_tac[]) >>
  metis_tac[LIST_REL_EL_EQN]
QED

Theorem dft_flip_frame_reach:
  !C g s0 j t. frame_reach C g s0 j t ==>
    !f. dft_flip_fn f g ==>
      ?i. frame_reach C f s0 i t /\ dft_flip_inst i j
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac >> rpt strip_tac
  >- (drule_all dft_flip_fn_active >> strip_tac >>
      qexists_tac `i` >> simp[] >>
      metis_tac[dft_flip_fn_entry, frame_reach_rules])
  >- (first_x_assum drule >> strip_tac >>
      drule_all dft_flip_fn_active >> strip_tac >>
      qexists_tac `i'` >> simp[] >>
      irule (cj 2 frame_reach_rules) >>
      metis_tac[dft_flip_inst_step, dft_flip_inst_terminator]) >>
  first_x_assum drule >> strip_tac >>
  drule_all dft_flip_fn_active >> strip_tac >>
  qexists_tac `i'` >> simp[] >>
  irule (cj 3 frame_reach_rules) >>
  metis_tac[dft_flip_inst_step, dft_flip_inst_terminator, dft_flip_fn_entry]
QED

Theorem dft_flip_inst_observation:
  inst_wf i /\ inst_shape_ok i /\ dft_flip_inst i j ==>
    mem_corr i t j t /\ call_corr i t j t
Proof
  strip_tac >>
  `mem_corr i t i t /\ call_corr i t i t` by
    (simp[mem_corr_def, call_corr_def] >> strip_tac >>
     metis_tac[dft_wf_invoke_decode]) >>
  fs[dft_flip_inst_def] >>
  metis_tac[dft_flip_inst_mem_ranges, dft_call_corr_flip_right, mem_corr_def]
QED

Theorem dft_flip_frame_sim:
  dft_swap_invariant L f /\ dft_flip_fn f g ==> frame_sim L C C f g
Proof
  rw[frame_sim_def] >> drule_all dft_flip_frame_reach >> strip_tac >>
  qexistsl [`i`, `s'`] >> simp[] >> irule dft_flip_inst_observation >>
  `active_inst f i s'` by metis_tac[frame_reach_active] >>
  fs[dft_swap_invariant_def, fn_inst_wf_def, fn_shape_ok_def, active_inst_def] >>
  `MEM i bb.bb_instructions` by metis_tac[MEM_EL] >>
  metis_tac[EVERY_fn_block, EVERY_MEM]
QED
