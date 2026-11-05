Theory abiScratchInput
Ancestors
  abiSiteEncoderContract abiScratchEncoderContract abiScratchEffect abiScratchFootprint abiDecoderFootprint
  abiDecoderReentry compileEnv venomState words arithmetic abiEncoderArrayFrame
  abiDecoderAllocation abiDecoderFrame valueEncoding contractABI pred_set list

(* ===== Effect ===== *)

(* The complete source contract remains available after a recursive encoding.
   TOP-LEVEL: abi_scratch_input_effect transports source values, live operands
   and physical separation through the actual root allocation evolution. *)

Theorem abi_site_input_mono:
  abi_site_encoder_input ei at av st src dst sb source_cap d sz A b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_site_encoder_input ei at av prepared src dst sb source_cap d sz A b cap s
Proof
  simp_tac bool_ss [abi_site_encoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_scratch_input_mono:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_input ei at av prepared src dst sb source_cap d sz first last b cap s
Proof
  rewrite_tac[GSYM abi_site_encoder_input_interval] >>
  MATCH_ACCEPT_TAC abi_site_input_mono
QED

Theorem abi_site_input_effect:
  abi_site_encoder_input ei at av st src dst sb source_cap d sz A b cap initial /\
  abi_site_encoder_effect A lo hi next limit_st d sz b cap initial actual /\
  st.cs_next_var <= next ==>
  abi_site_encoder_input ei at av st src dst sb source_cap d sz A b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_site_effect_source >> disch_tac >>
  qhdtm_assum `abi_site_encoder_input`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_encoder_input_def]) >>
  `abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (imp_res_tac abi_site_effect_operand >> asm_simp_tac bool_ss []) >>
  `abi_scratch_evolution A b cap initial actual /\ FINITE A` by
    fs[abi_site_encoder_effect_def, abiSiteAllocationTheory.abi_site_budget_def] >>
  `abi_footprint_disjoint sb source_cap
     (abi_decoder_child_scratch A b cap actual) /\
   abi_footprint_disjoint d sz
     (abi_decoder_child_scratch A b cap actual)` by
    (conj_tac >> irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_site_encoder_input_def]
QED

Theorem abi_scratch_input_effect:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap initial /\
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
  first <= lo /\ hi <= last /\ st.cs_next_var <= next ==>
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap actual
Proof
  rpt strip_tac >>
  `abi_site_encoder_effect (abi_decoder_ids first last) lo hi next limit_st d sz b cap initial actual` by
    (asm_simp_tac bool_ss [abi_site_encoder_effect_interval]) >>
  fs[GSYM abi_site_encoder_input_interval] >> drule_all abi_site_input_effect >> simp[]
QED

(* ===== Regions ===== *)

(* Child inputs inherit physical separation from their enclosing buffers.
   TOP-LEVEL: abi_scratch_input_regions transfers complete child data and
   bounded subregions across allocator evolution, including reused sites. *)

Theorem abi_site_input_regions:
  abi_site_encoder_input parent_ei parent_at parent_av st parent_src parent_dst
    sb source_cap d output_size A b cap initial /\
  FINITE A /\ abi_scratch_evolution A b cap initial actual /\
  abi_encoder_input ei at av child_sb child_cap actual.vs_memory /\
  eval_operand src actual = SOME (n2w child_sb) /\ eval_operand dst actual = SOME (n2w child_d) /\
  abi_decoder_operand_live prepared.cs_next_var src /\
  abi_decoder_operand_live prepared.cs_next_var dst /\
  sb <= child_sb /\ child_sb+child_cap <= sb+source_cap /\
  d <= child_d /\ child_d+child_size <= d+output_size /\ LENGTH (enc at av) <= child_size ==>
  abi_site_encoder_input ei at av prepared src dst child_sb child_cap child_d child_size
    A b cap actual
Proof
  strip_tac >>
  qpat_x_assum `abi_site_encoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_encoder_input_def]) >>
  `abi_footprint_disjoint child_sb child_cap (abi_decoder_child_scratch A b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`, `source_cap`] >> simp[]) >>
  `abi_footprint_disjoint child_d child_size (abi_decoder_child_scratch A b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`, `output_size`] >> simp[]) >>
  `abi_footprint_disjoint child_sb child_cap (abi_decoder_child_scratch A b cap actual)` by
    (irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  `abi_footprint_disjoint child_d child_size (abi_decoder_child_scratch A b cap actual)` by
    (irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_site_encoder_input_def] >> decide_tac
QED

Theorem abi_scratch_input_regions:
  abi_scratch_input parent_ei parent_at parent_av st parent_src parent_dst
    sb source_cap d output_size first last b cap initial /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
  abi_encoder_input ei at av child_sb child_cap actual.vs_memory /\
  eval_operand src actual = SOME (n2w child_sb) /\ eval_operand dst actual = SOME (n2w child_d) /\
  abi_decoder_operand_live prepared.cs_next_var src /\
  abi_decoder_operand_live prepared.cs_next_var dst /\
  sb <= child_sb /\ child_sb+child_cap <= sb+source_cap /\
  d <= child_d /\ child_d+child_size <= d+output_size /\ LENGTH (enc at av) <= child_size ==>
  abi_scratch_input ei at av prepared src dst child_sb child_cap child_d child_size
    first last b cap actual
Proof
  rewrite_tac[GSYM abi_site_encoder_input_interval] >>
  strip_tac >> drule abi_site_input_regions >> simp[]
QED
