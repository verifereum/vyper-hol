(* Entry and completed-prefix synchronization across a directed swap. *)
Theory dftFrameSync
Ancestors
  dftFrameAnchor dftFrameLocal dftFrameLegal dftFrameSwap dftFramePair
  contextCodegenRel venomExecSemantics venomExecProofs venomInst venomWf dftFramePerm unitShapeDefs
  o1PassLift dftFramePrefix dftCorrectnessFinal cfgNormSim ctxLookupAgreeHelpers list rich_list arithmetic

Theorem dft_nonphi_swap_entry_list:
  !pre a b post. a.inst_opcode <> PHI /\ b.inst_opcode <> PHI ==>
    eval_phis s (pre ++ a::b::post) = eval_phis s (pre ++ b::a::post) /\
    phi_prefix_length (pre ++ a::b::post) =
    phi_prefix_length (pre ++ b::a::post)
Proof
  Induct >> simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem dft_swap_list_entry:
  dft_swap_list xs ys ==>
    eval_phis s xs = eval_phis s ys /\
    phi_prefix_length xs = phi_prefix_length ys
Proof
  simp[dft_swap_list_def, adjacent_swap_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> irule dft_nonphi_swap_entry_list >>
  fs[dft_cross_def] >> metis_tac[is_pseudo_def]
QED

Theorem dft_swap_fn_entry:
  dft_swap_fn f g ==> (enters_block f v e <=> enters_block g v e)
Proof
  simp[dft_swap_fn_def] >> strip_tac >>
  `eval_phis v bb.bb_instructions = eval_phis v insts /\
   phi_prefix_length bb.bb_instructions = phi_prefix_length insts` by
    metis_tac[dft_swap_list_entry] >>
  gvs[enters_block_def, lookup_block_APPEND] >>
  Cases_on `lookup_block v.vs_current_bb p` >> simp[] >>
  simp[lookup_block_def, FIND_thm] >>
  Cases_on `bb.bb_label = v.vs_current_bb` >> simp[] >> metis_tac[]
QED

Theorem dft_swap_fn_active_exists:
  dft_swap_fn f g /\ active_inst g j t ==> ?i. active_inst f i t
Proof
  simp[active_inst_def] >> strip_tac >>
  drule_all dft_swap_fn_block_backward >> strip_tac >>
  `LENGTH bb.bb_instructions = LENGTH bb'.bb_instructions` by
    (fs[relationTheory.RC_DEF] >>
     metis_tac[dft_swap_list_perm, sortingTheory.PERM_LENGTH]) >>
  qexists_tac `bb'` >> simp[] >> metis_tac[]
QED

Theorem dft_legal_swap_fn_entry:
  dft_swap_invariant L f /\ dft_legal_swap_fn f g ==>
  (enters_block f v e <=> enters_block g v e)
Proof
  metis_tac[dft_legal_swap_fn_projection, dft_swap_fn_entry]
QED

Theorem dft_block_anchor_reach:
  wf_function f /\ dft_block_anchor C f f s0 j t ==>
  frame_reach C f s0 j t
Proof
  simp[dft_block_anchor_def] >> strip_tac >>
  `active_inst f i e` by metis_tac[frame_reach_active] >>
  `i = HD (xs ++ [j])` by
    (fs[active_inst_def] >>
     `bb' = bb` by metis_tac[wf_fn_blocks_same_label_eq] >> gvs[] >>
     Cases_on `xs` >> gvs[EL_APPEND_EQN]) >>
  irule dft_prefix_frame_reach >>
  qexistsl [`bb`, `xs`, `post`, `pre`, `e`] >>
  simp[APPEND_ASSOC] >> metis_tac[]
QED

(* A terminator cut never splits a non-terminating commutable pair. *)
Theorem dft_pair_prefix_cut:
  !p xs s t j post.
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    (!u v. dft_prefix C [a;b] u v <=> dft_prefix C [b;a] u v) /\
    xs ++ j::post = p ++ b::a::q /\
    is_terminator j.inst_opcode /\ dft_prefix C xs s t ==>
    ?ys post'. p ++ a::b::q = ys ++ j::post' /\ dft_prefix C ys s t
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> Cases_on `xs` >> gvs[] >>
      rename1 `dft_prefix C (b::rest) s t` >>
      Cases_on `rest` >> gvs[] >>
      rename1 `dft_prefix C (b::a::tail) s t` >>
      qexistsl [`a::b::tail`, `post`] >> simp[] >>
      `dft_prefix C ([b;a] ++ tail) s t` by simp[] >>
      qpat_x_assum `dft_prefix C (b::a::tail) s t` kall_tac >>
      `dft_prefix C ([a;b] ++ tail) s t` suffices_by simp[] >>
      gvs[dft_prefix_append] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `xs` >> gvs[]
  >- (qexistsl [`[]`, `p ++ a::b::q`] >> simp[]) >>
  qpat_x_assum `dft_prefix C (_::_) s t` mp_tac >>
  pure_once_rewrite_tac[dft_prefix_cons] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `p ++ [a;b] ++ q = ys ++ [j] ++ suffix` >>
  qexistsl [`h::ys`, `suffix`] >> simp[dft_prefix_cons] >> metis_tac[]
QED

Theorem dft_pair_skip_phi:
  !p n. a.inst_opcode <> PHI /\ b.inst_opcode <> PHI /\
    n <= phi_prefix_length (p ++ b::a::q) ==>
    TAKE n (p ++ a::b::q) = TAKE n (p ++ b::a::q) /\
    ?r. DROP n (p ++ a::b::q) = r ++ a::b::q /\
        DROP n (p ++ b::a::q) = r ++ b::a::q
Proof
  Induct >> Cases_on `n` >> simp[phi_prefix_length_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  first_x_assum drule_all >> metis_tac[]
QED

Theorem dft_swap_list_terminator_prefix:
  dft_swap_list src dst /\
  EVERY (\i. inst_wf i /\ inst_shape_ok i /\ i.inst_opcode <> ALLOCA) src /\
  dst = pre ++ xs ++ j::post /\
  LENGTH pre <= phi_prefix_length dst /\
  is_terminator j.inst_opcode /\ dft_prefix C xs s t ==>
  ?pre' ys post'. src = pre' ++ ys ++ j::post' /\
    LENGTH pre' = LENGTH pre /\ dft_prefix C ys s t
Proof
  simp[dft_swap_list_def, adjacent_swap_def] >> strip_tac >> gvs[] >>
  `a.inst_opcode <> PHI /\ b.inst_opcode <> PHI /\
   ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode` by
    (fs[dft_cross_def] >> metis_tac[is_pseudo_def]) >>
  `!u v. dft_prefix C [a;b] u v <=> dft_prefix C [b;a] u v` by
    (irule dft_cross_prefix_pair >> fs[EVERY_APPEND]) >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule_all dft_pair_skip_phi >> strip_tac >>
  `xs ++ j::post = r ++ b::a::q` by
    metis_tac[DROP_LENGTH_APPEND, APPEND_ASSOC] >>
  drule_all dft_pair_prefix_cut >> strip_tac >>
  qexistsl [`TAKE (LENGTH pre) (p ++ [a;b] ++ q)`, `ys`, `post'`] >>
  conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      qspecl_then [`LENGTH pre`, `p ++ a::b::q`] mp_tac TAKE_DROP >>
      asm_simp_tac std_ss [GSYM APPEND_ASSOC] >> metis_tac[]) >>
  `TAKE (LENGTH pre) (p ++ a::b::q) = pre` by
    metis_tac[TAKE_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_simp_tac std_ss []
QED

Theorem dft_entry_phi_index:
  wf_function f /\ enters_block f v e /\
  MEM bb f.fn_blocks /\ bb.bb_label = e.vs_current_bb ==>
  e.vs_inst_idx = phi_prefix_length bb.bb_instructions
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  `MEM bb' f.fn_blocks /\ bb'.bb_label = v.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `bb' = bb` by metis_tac[wf_fn_blocks_same_label_eq] >> gvs[]
QED

Theorem dft_invariant_block_steps[local]:
  dft_swap_invariant L f /\ MEM bb f.fn_blocks ==>
  EVERY (\i. inst_wf i /\ inst_shape_ok i /\ i.inst_opcode <> ALLOCA)
    bb.bb_instructions
Proof
  strip_tac >> fs[dft_swap_invariant_def, fn_shape_ok_def] >>
  drule_all EVERY_fn_block >> strip_tac >>
  `EVERY inst_shape_ok bb.bb_instructions` by metis_tac[EVERY_fn_block] >>
  fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]
QED

Theorem dft_swap_terminator_anchor:
  dft_swap_invariant L f /\ dft_swap_fn f g /\
  dft_block_anchor C f g s0 j t /\ is_terminator j.inst_opcode ==>
  frame_reach C f s0 j t
Proof
  strip_tac >>
  `wf_function f /\ wf_function g` by
    metis_tac[dft_swap_invariant_def, dft_swap_fn_wf] >>
  fs[dft_block_anchor_def] >>
  `e.vs_inst_idx = phi_prefix_length bb.bb_instructions` by
    metis_tac[dft_entry_phi_index] >>
  drule_all dft_swap_fn_block_backward >> strip_tac >>
  `enters_block f v e` by metis_tac[dft_swap_fn_entry] >>
  `EVERY (\i. inst_wf i /\ inst_shape_ok i /\ i.inst_opcode <> ALLOCA)
     bb'.bb_instructions` by metis_tac[dft_invariant_block_steps] >>
  `?pre' ys post'. bb'.bb_instructions = pre' ++ ys ++ j::post' /\
     LENGTH pre' = LENGTH pre /\ dft_prefix C ys e t` by
    (`LENGTH pre <= phi_prefix_length bb.bb_instructions` by simp[] >>
     Cases_on `bb'.bb_instructions = bb.bb_instructions`
     >- (qexistsl [`pre`, `xs`, `post`] >> simp[APPEND_ASSOC]) >>
     `dft_swap_list bb'.bb_instructions bb.bb_instructions` by
       metis_tac[relationTheory.RC_DEF] >>
     rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
     drule_all (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
       dft_swap_list_terminator_prefix) >> simp[APPEND_ASSOC]) >>
  irule dft_block_anchor_reach >> simp[] >>
  simp[dft_block_anchor_def] >>
  qexistsl [`v`, `e`, `bb'`, `pre'`, `ys`, `post'`, `i`] >> simp[] >> metis_tac[]
QED

Theorem dft_legal_swap_terminator_anchor:
  dft_swap_invariant L f /\ dft_legal_swap_fn f g /\
  dft_block_anchor C f g s0 j t /\ is_terminator j.inst_opcode ==>
  frame_reach C f s0 j t
Proof
  metis_tac[dft_swap_terminator_anchor, dft_legal_swap_fn_projection]
QED
