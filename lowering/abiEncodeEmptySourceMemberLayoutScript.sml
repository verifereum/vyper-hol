(* Output layout boundaries independent of any live source window. *)
Theory abiEncodeEmptySourceMemberLayout
Ancestors
  abiEncoderWindowStructuralMembers abiEncoderWindowMembers abiEncoderInput
  abiEncoderWindowPhase abiCanonicalWindows valueEncodingProps contractABI
  abiEncoderRegisteredEffect abiEncoderWindowContract
  venomMemDefs list rich_list arithmetic

Theorem empty_source_member_output_bounds:
  LIST_REL abi_encoder_structural_valid ats avs /\ LENGTH ats = LENGTH avs /\
  k < LENGTH ats /\ abi_encoder_tuple_type at ats /\
  window_member_head_size infos = head_lengths ats 0 ==>
  (is_dynamic (EL k ats) ==>
    SUM (MAP abi_member_head_size (TAKE k ats)) + 32 <= window_member_head_size infos /\
    window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
      LENGTH (enc at (ListV avs))) /\
  (~is_dynamic (EL k ats) ==>
    SUM (MAP abi_member_head_size (TAKE k ats)) + LENGTH (enc (EL k ats) (EL k avs)) <=
      window_member_head_size infos)
Proof
  strip_tac >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (fs[abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
  asm_rewrite_tac[window_member_tail_def] >>
  conj_tac >- metis_tac[window_structural_member_dynamic_bounds] >>
  metis_tac[window_structural_member_static_bounds]
QED

Theorem empty_source_member_total_bounds:
  LIST_REL abi_encoder_structural_valid ats avs /\ LENGTH ats = LENGTH avs /\
  k < LENGTH ats /\ abi_encoder_tuple_type at ats /\
  window_member_head_size infos = head_lengths ats 0 ==>
  window_member_head_size infos <= LENGTH (enc at (ListV avs)) /\
  window_member_tail infos ats avs k <= LENGTH (enc at (ListV avs))
Proof
  strip_tac >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (fs[abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
  drule window_structural_member_tuple_length >>
  drule_all window_member_tail_bound >>
  simp[window_member_tail_def] >> decide_tac
QED

Theorem empty_source_member_static_prefix_frame:
  LIST_REL abi_encoder_structural_valid ats avs /\ LENGTH ats = LENGTH avs /\
  k < LENGTH ats /\ abi_encoder_tuple_type at ats /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  ~is_dynamic (EL k ats) /\
  d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
  window_phase ctx func st en ids
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
      LENGTH (enc (EL k ats) (EL k avs)))] s t ==>
  window_member_prefix infos ats avs k d t.vs_memory
Proof
  strip_tac >>
  `k <= LENGTH ats` by decide_tac >>
  drule_all window_structural_member_prefix_layout >> strip_tac >>
  drule_all empty_source_member_output_bounds >> strip_tac >>
  drule_all empty_source_member_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) <= head_lengths ats 0` by gvs[] >>
  drule window_phase_effect >> strip_tac >>
  drule window_phase_resources >> strip_tac >>
  irule window_member_prefix_frame >>
  qexistsl_tac [`ids`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),
       LENGTH (enc (EL k ats) (EL k avs)))]`, `s`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- simp[venomMemDefsTheory.regions_disjoint_def, EVERY_DEF]) >>
  (conj_tac >- (simp[venomMemDefsTheory.regions_disjoint_def, EVERY_DEF,
      window_member_tail_def] >> gvs[])) >>
  reverse conj_tac >- gvs[] >> rpt gen_tac >> strip_tac >>
  `venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    metis_tac[] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
  qpat_x_assum `window_member_tail infos ats avs k <= _` mp_tac >>
  pure_rewrite_tac[window_member_tail_def, venomMemDefsTheory.regions_disjoint_def] >>
  pure_asm_rewrite_tac[] >> decide_tac
QED

Theorem empty_source_member_dynamic_prefix_frame:
  LIST_REL abi_encoder_structural_valid ats avs /\ LENGTH ats = LENGTH avs /\
  k < LENGTH ats /\ abi_encoder_tuple_type at ats /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_prefix infos ats avs k d s.vs_memory /\
  is_dynamic (EL k ats) /\
  d + LENGTH (enc at (ListV avs)) <= s.vs_alloca_next /\
  (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)) /\
  window_phase ctx func st en ids
    [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
     (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t ==>
  window_member_prefix infos ats avs k d t.vs_memory
Proof
  strip_tac >>
  `k <= LENGTH ats` by decide_tac >>
  drule_all window_structural_member_prefix_layout >> strip_tac >>
  drule_all empty_source_member_output_bounds >> strip_tac >>
  drule_all empty_source_member_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) <= head_lengths ats 0` by gvs[] >>
  drule window_phase_effect >> strip_tac >>
  drule window_phase_resources >> strip_tac >>
  irule window_member_prefix_frame >>
  qexistsl_tac [`ids`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`, `s`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- (simp[venomMemDefsTheory.regions_disjoint_def, EVERY_DEF,
      window_member_tail_def] >> gvs[])) >>
  (conj_tac >- (simp[venomMemDefsTheory.regions_disjoint_def, EVERY_DEF,
      window_member_tail_def] >> gvs[])) >>
  reverse conj_tac >- gvs[] >> rpt gen_tac >> strip_tac >>
  `venomMemDefs$regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,sz)` by
    metis_tac[] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,_) (b,sz)` mp_tac >>
  qpat_x_assum `window_member_tail infos ats avs k <= _` mp_tac >>
  pure_rewrite_tac[window_member_tail_def, venomMemDefsTheory.regions_disjoint_def] >>
  pure_asm_rewrite_tac[] >> decide_tac
QED

Theorem empty_source_member_static_cursor_frame:
  window_phase ctx func st mid ids [(q,n)] s t /\ site NOTIN ids /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  venomMemDefs$regions_disjoint (slot,32) (q,n) ==>
  mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at slot 32 t.vs_memory = mem_bytes_at slot 32 s.vs_memory` by
    (irule abi_encoder_window_effect_parent >>
     (conj_tac >- metis_tac[window_phase_resources]) >>
     qexistsl_tac [`ids`, `[(q,n)]`, `site`] >> simp[] >>
     metis_tac[window_phase_effect, window_phase_resources]) >>
  simp_tac bool_ss [abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  asm_rewrite_tac[]
QED
