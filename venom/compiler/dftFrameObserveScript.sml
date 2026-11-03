(* Observation witnesses at arbitrary cuts of a legal adjacent swap. *)
Theory dftFrameObserve
Ancestors
  dftFrameSync dftFrameContext dftFrameAnchor dftFramePrefix dftFrameLocal dftFrameLegal
  dftFrameSwap dftFramePair dftFrameFacts o1PassLift contextCodegenRel
  venomExecSemantics venomExecProofs venomInstProofs venomWf venomInst unitShapeDefs
  ctxLookupAgreeHelpers list rich_list arithmetic

Theorem dft_pair_cut_positions:
  !p xs j post. xs ++ j::post = p ++ b::a::q ==>
    (?r. p = xs ++ j::r) \/
    (xs = p /\ j = b) \/
    (xs = p ++ [b] /\ j = a) \/
    (?r. xs = p ++ b::a::r /\ q = r ++ j::post)
Proof
  Induct
  >- (Cases >> simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
      Cases_on `t` >> gvs[] >> metis_tac[]) >>
  gen_tac >> Cases >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
QED

Theorem dft_pair_prefix_cases:
  (!u v. dft_prefix C [a;b] u v <=> dft_prefix C [b;a] u v) /\
  xs ++ j::post = p ++ b::a::q /\ dft_prefix C xs s t ==>
  (?ys post'. p ++ a::b::q = ys ++ j::post' /\ dft_prefix C ys s t) \/
  (j = b /\ dft_prefix C p s t) \/
  (j = a /\ ?u fuel v. dft_prefix C p s u /\
    step_inst fuel C b u = OK v /\ t = v with vs_inst_idx := SUC u.vs_inst_idx)
Proof
  strip_tac >> drule dft_pair_cut_positions >> strip_tac
  >- (disj1_tac >> qexistsl [`xs`, `r ++ a::b::q`] >> simp[APPEND_ASSOC])
  >- (gvs[] >> metis_tac[])
  >- (gvs[] >> disj2_tac >> disj2_tac >> fs[dft_prefix_append, dft_prefix_cons] >>
      metis_tac[]) >>
  disj1_tac >> qexistsl [`p ++ a::b::r`, `post`] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  `dft_prefix C (p ++ ([b;a] ++ r)) s t` by fs[APPEND_ASSOC] >>
  `dft_prefix C (p ++ ([a;b] ++ r)) s t` suffices_by (pure_rewrite_tac[APPEND] >> simp[]) >>
  fs[dft_prefix_append] >> metis_tac[]
QED

Theorem dft_after_first_target_observation:
  frame_reach C f s0 a s /\ dft_cross a b /\
  inst_wf a /\ inst_wf b /\ inst_shape_ok a /\ inst_shape_ok b /\
  a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA /\
  step_inst fuel C b s = OK t ==>
  ?i u. frame_reach C f s0 i u /\
    mem_corr i u a (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    call_corr i u a (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> qexistsl [`a`, `s`] >> simp[] >>
  irule dft_cross_step_observation_left >> metis_tac[]
QED

Theorem dft_before_first_target_observation:
  dft_swap_invariant s.vs_labels f /\
  fn_entry_label f = SOME s0.vs_current_bb /\
  frame_reach C f s0 a s /\ dft_legal_cross a b /\
  active_inst f b (s with vs_inst_idx := SUC s.vs_inst_idx) /\
  inst_wf a /\ inst_wf b /\ inst_shape_ok a /\ inst_shape_ok b /\
  a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA ==>
  ?i u. frame_reach C f s0 i u /\ mem_corr i u b s /\ call_corr i u b s
Proof
  strip_tac >> Cases_on `inst_mem_ranges b s = [] /\ b.inst_opcode <> INVOKE`
  >- (qexistsl [`a`, `s`] >> fs[mem_corr_def, call_corr_def]) >>
  `?t. step_inst 0 C a s = OK t` by
    (irule dft_legal_observed_predecessor_total >> metis_tac[]) >>
  `dft_cross a b /\ ~is_terminator a.inst_opcode` by
    fs[dft_legal_cross_def, dft_cross_def] >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `active_inst f b (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (fs[active_inst_def] >> metis_tac[]) >>
  qexistsl [`b`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule (cj 2 frame_reach_rules) >> metis_tac[]) >>
  irule dft_cross_step_observation_right >> metis_tac[]
QED

Theorem dft_legal_swap_list_prefix_cases:
  dft_legal_swap_list src dst /\
  EVERY (\i. inst_wf i /\ inst_shape_ok i /\ i.inst_opcode <> ALLOCA) src /\
  dst = pre ++ xs ++ j::post /\
  LENGTH pre <= phi_prefix_length dst /\ dft_prefix C xs s t ==>
  (?pre' ys post'. src = pre' ++ ys ++ j::post' /\
    LENGTH pre' = LENGTH pre /\ dft_prefix C ys s t) \/
  (?a b pre' p q. dft_legal_cross a b /\
    inst_wf a /\ inst_wf b /\ inst_shape_ok a /\ inst_shape_ok b /\
    a.inst_opcode <> ALLOCA /\ b.inst_opcode <> ALLOCA /\
    src = pre' ++ p ++ a::b::q /\ LENGTH pre' = LENGTH pre /\
    ((j = b /\ dft_prefix C p s t) \/
     (j = a /\ ?u fuel v. dft_prefix C p s u /\
       step_inst fuel C b u = OK v /\ t = v with vs_inst_idx := SUC u.vs_inst_idx)))
Proof
  simp[dft_legal_swap_list_def, dftFramePermTheory.adjacent_swap_def] >>
  strip_tac >> gvs[] >>
  `dft_cross a b` by metis_tac[dft_legal_cross_projection] >>
  `a.inst_opcode <> PHI /\ b.inst_opcode <> PHI` by
    (fs[dft_cross_def] >> metis_tac[is_pseudo_def]) >>
  `!u v. dft_prefix C [a;b] u v <=> dft_prefix C [b;a] u v` by
    (irule dft_cross_prefix_pair >> fs[EVERY_APPEND]) >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule_all dft_pair_skip_phi >> strip_tac >>
  `xs ++ j::post = r ++ b::a::q` by
    metis_tac[DROP_LENGTH_APPEND, APPEND_ASSOC] >>
  `TAKE (LENGTH pre) (p ++ a::b::q) = pre` by
    metis_tac[TAKE_LENGTH_APPEND] >>
  `p ++ a::b::q = pre ++ r ++ a::b::q` by
    (qspecl_then [`LENGTH pre`, `p ++ a::b::q`] mp_tac TAKE_DROP >>
     asm_simp_tac std_ss [GSYM APPEND_ASSOC]) >>
  drule_all dft_pair_prefix_cases >> strip_tac
  >- (disj1_tac >> qexistsl [`pre`, `ys`, `post'`] >>
      asm_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]) >>
  disj2_tac >> qexistsl [`a`, `b`, `pre`, `r`, `q`] >>
  asm_simp_tac std_ss [GSYM APPEND_ASSOC, APPEND] >>
  fs[EVERY_APPEND] >> metis_tac[]
QED

Theorem dft_legal_swap_fn_block_backward:
  dft_legal_swap_fn f g /\ MEM bb' g.fn_blocks ==>
  ?bb. MEM bb f.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    RC dft_legal_swap_list bb.bb_instructions bb'.bb_instructions
Proof
  rw[dft_legal_swap_fn_def] >> gvs[MEM_APPEND] >>
  metis_tac[relationTheory.RC_DEF, basic_block_accfupds, basic_block_fupdfupds]
QED

Theorem dft_source_prefix_reach:
  wf_function f /\ enters_block f v e /\ frame_reach C f s0 i e /\
  MEM bb f.fn_blocks /\ bb.bb_label = e.vs_current_bb /\
  bb.bb_instructions = pre ++ xs ++ j::post /\
  LENGTH pre = e.vs_inst_idx /\ dft_prefix C xs e t ==>
  frame_reach C f s0 j t
Proof
  strip_tac >> irule dft_block_anchor_reach >> simp[] >>
  simp[dft_block_anchor_def] >>
  qexistsl [`v`, `e`, `bb`, `pre`, `xs`, `post`, `i`] >> simp[]
QED

Theorem dft_reachable_reflexive_observation:
  fn_inst_wf f /\ frame_reach C f s0 j t ==>
  mem_corr j t j t /\ call_corr j t j t
Proof
  strip_tac >> `active_inst f j t` by metis_tac[frame_reach_active] >>
  `inst_wf j` by (fs[active_inst_def, fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  simp[mem_corr_def, call_corr_def] >> strip_tac >>
  metis_tac[dft_wf_invoke_decode]
QED

Theorem dft_legal_anchor_observation:
  dft_swap_invariant L f /\ dft_legal_swap_fn f g /\
  fn_entry_state f s0 /\ s0.vs_labels = L /\ dft_block_anchor C f g s0 j t ==>
  ?i s. frame_reach C f s0 i s /\ mem_corr i s j t /\ call_corr i s j t
Proof
  strip_tac >>
  `dft_swap_fn f g` by metis_tac[dft_legal_swap_fn_projection] >>
  `wf_function f /\ wf_function g /\ fn_inst_wf f` by
    metis_tac[dft_swap_invariant_def, dft_swap_fn_wf] >>
  fs[dft_block_anchor_def] >>
  `e.vs_inst_idx = phi_prefix_length bb.bb_instructions` by
    metis_tac[dft_entry_phi_index] >>
  drule_all dft_legal_swap_fn_block_backward >> strip_tac >>
  `enters_block f v e /\ bb'.bb_label = e.vs_current_bb` by
    metis_tac[dft_swap_fn_entry] >>
  `EVERY (\i. inst_wf i /\ inst_shape_ok i /\ i.inst_opcode <> ALLOCA)
     bb'.bb_instructions` by
    (fs[dft_swap_invariant_def, fn_shape_ok_def] >>
     drule_all EVERY_fn_block >> strip_tac >>
     `EVERY inst_shape_ok bb'.bb_instructions` by metis_tac[EVERY_fn_block] >>
     fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  Cases_on `bb'.bb_instructions = bb.bb_instructions`
  >- suspend "unchanged" >>
  `dft_legal_swap_list bb'.bb_instructions bb.bb_instructions` by
    metis_tac[relationTheory.RC_DEF] >>
  `LENGTH pre <= phi_prefix_length bb.bb_instructions` by simp[] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
    dft_legal_swap_list_prefix_cases) >> strip_tac
  >- suspend "exact"
  >- suspend "before_pair" >>
  suspend "between_pair"
QED

Resume dft_legal_anchor_observation[unchanged]:
  `bb'.bb_instructions = pre ++ xs ++ j::post` by fs[APPEND_ASSOC] >>
  `frame_reach C f s0 j t` by
    (rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
     drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
       dft_source_prefix_reach) >> simp[]) >>
  qexistsl [`j`, `t`] >> simp[] >>
  irule dft_reachable_reflexive_observation >> metis_tac[]
QED
Resume dft_legal_anchor_observation[exact]:
  `LENGTH pre' = e.vs_inst_idx` by simp[] >>
  `frame_reach C f s0 j t` by
    (drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
       dft_source_prefix_reach) >> simp[]) >>
  qexistsl [`j`, `t`] >> simp[] >>
  irule dft_reachable_reflexive_observation >> metis_tac[]
QED
Resume dft_legal_anchor_observation[before_pair]:
  `LENGTH pre' = e.vs_inst_idx` by simp[] >>
  `frame_reach C f s0 a t` by
    (drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
       dft_source_prefix_reach) >> simp[]) >>
  `t.vs_labels = L` by metis_tac[dft_frame_reach_labels] >>
  `t.vs_current_bb = e.vs_current_bb /\
   t.vs_inst_idx = e.vs_inst_idx + LENGTH p` by
    metis_tac[dft_prefix_control] >>
  `active_inst f b (t with vs_inst_idx := SUC t.vs_inst_idx)` by
    (simp[active_inst_def] >> qexists_tac `bb'` >>
     simp[EL_APPEND_EQN, ADD1]) >>
  gvs[] >> irule dft_before_first_target_observation >>
  fs[fn_entry_state_def] >> metis_tac[]
QED
Resume dft_legal_anchor_observation[between_pair]:
  `LENGTH pre' = e.vs_inst_idx` by simp[] >>
  `frame_reach C f s0 a u` by
    (drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
       dft_source_prefix_reach) >> simp[]) >>
  gvs[] >> irule dft_after_first_target_observation >>
  metis_tac[dft_legal_cross_projection]
QED
Finalise dft_legal_anchor_observation
