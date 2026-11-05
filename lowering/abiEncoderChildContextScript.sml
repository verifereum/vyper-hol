(* Extract the three dynamic-child phases with their actual enclosing code. *)
Theory abiEncoderChildContext
Ancestors
  abiDecoderSiteMembership pred_set
  abiEncoderAddressReach abiEncoderChildCode abiEncoderAppend abiEncoderCounters abiEncoderResultLive
  abiDecoderReentry abiDecoderContract fragExec compileEnv emitHelperProps list rich_list arithmetic

Theorem abi_encoder_straight_extends:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' ==>
  cs_extends st st'
Proof
  strip_tac >> irule cs_extends_same_block >>
  gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]
QED

Theorem abi_encoder_dynamic_child_context:
  compile_abi_encode_child dst src ei T head_offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?ops prepared child_len child_end.
    abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,prepared) /\
    compile_abi_encode_to_buf (SND (SND ops)) src ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix (FST ops) dyn_ptr (FST (SND ops)) child_len child_end = (out,end_st) /\
    fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
    prepared.cs_next_var = st.cs_next_var+3 /\ prepared.cs_next_id = st.cs_next_id+3 /\
    prepared.cs_blocks = st.cs_blocks /\
    child_end.cs_next_var+1 = end_st.cs_next_var /\ child_end.cs_next_id+3 = end_st.cs_next_id /\
    end_st.cs_blocks = child_end.cs_blocks /\ end_st.cs_current_bb = child_end.cs_current_bb /\
    prepared.cs_next_var <= child_end.cs_next_var /\ prepared.cs_next_id <= child_end.cs_next_id /\
    abi_decoder_operand_live child_end.cs_next_var child_len
Proof
  strip_tac >> drule abi_encode_dynamic_child_trace >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule abi_encode_result_live >> strip_tac >>
  `cs_extends st prepared` by (irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  `cs_extends child_end end_st` by (irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  `cs_extends prepared child_end` by (drule cs_extends_abi_encode >> simp[]) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `child_end` >> simp[]) >>
  mp_tac (Q.SPECL [`st`, `prepared`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`prepared`, `child_end`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`ops`, `prepared`, `child_len`, `child_end`] >> simp[]
QED

Theorem abi_encoder_static_child_structural_context:
  compile_abi_encode_child dst src ei F offset dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?head prepared. emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) /\
    compile_abi_encode_to_buf head src ei prepared = (out,end_st) /\
    fn_has_code st prepared func /\ fn_has_code prepared end_st func /\
    prepared.cs_next_var = st.cs_next_var+1 /\ prepared.cs_next_id = st.cs_next_id+1 /\
    prepared.cs_blocks = st.cs_blocks /\
    prepared.cs_next_var <= end_st.cs_next_var /\ prepared.cs_next_id <= end_st.cs_next_id /\
    abi_decoder_operand_live prepared.cs_next_var head
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >> drule_all fn_has_code_split >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  qexistsl_tac [`head`, `prepared`] >> asm_simp_tac bool_ss []
QED

Definition abi_encoder_hereditary_guard_def:
  abi_encoder_hereditary_guard G <=>
    !a p q z. G a z /\ cs_extends a p /\ cs_extends p q /\ cs_extends q z /\
      a.cs_next_id <= p.cs_next_id /\ q.cs_next_id <= z.cs_next_id ==> G p q
End

Theorem abi_encoder_hereditary_guard_interval:
  abi_encoder_hereditary_guard
    (\st en. first <= st.cs_next_id /\ en.cs_next_id <= last)
Proof
  simp_tac bool_ss [abi_encoder_hereditary_guard_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_encoder_hereditary_guard_sites:
  abi_encoder_hereditary_guard
    (\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A)
Proof
  simp_tac bool_ss [abi_encoder_hereditary_guard_def] >> rpt strip_tac >>
  irule SUBSET_TRANS >>
  goal_assum (drule_at (Pat `_ SUBSET A`)) >>
  irule abi_decoder_emitted_sites_subsegment >> asm_rewrite_tac []
QED

Theorem abi_encoder_static_child_guard:
  abi_encoder_hereditary_guard G /\ G st en /\
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) ==>
  G prepared en
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >> gvs[] >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cs_extends prepared en` by (drule cs_extends_abi_encode >> simp[]) >>
  `cs_extends en en` by simp[cs_extends_refl] >>
  qpat_x_assum `abi_encoder_hereditary_guard G` mp_tac >>
  simp_tac bool_ss [abi_encoder_hereditary_guard_def] >>
  disch_then irule >> asm_rewrite_tac [] >>
  qexistsl_tac [`st`,`en`] >> asm_rewrite_tac [] >> decide_tac
QED

Theorem abi_encoder_dynamic_child_guard:
  abi_encoder_hereditary_guard G /\ G st en /\
  compile_abi_encode_child dst src ei T offset dp st = (out,en) /\
  abi_encode_child_prefix dst offset dp st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND (SND ops)) src ei prepared = (len,child_end) ==>
  G prepared child_end
Proof
  strip_tac >> drule abi_encode_dynamic_child_trace >> strip_tac >> gvs[] >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  `cs_extends st prepared` by
    (irule abi_encoder_straight_extends >> simp[]) >>
  `cs_extends child_end en` by
    (irule abi_encoder_straight_extends >> simp[]) >>
  `cs_extends prepared child_end` by (drule cs_extends_abi_encode >> simp[]) >>
  qpat_x_assum `abi_encoder_hereditary_guard G` mp_tac >>
  simp_tac bool_ss [abi_encoder_hereditary_guard_def] >>
  disch_then irule >> asm_rewrite_tac [] >>
  qexistsl_tac [`st`,`en`] >> asm_rewrite_tac [] >> decide_tac
QED

(* The site guard is inherited by the actual recursive compiler invocation,
   without an assumption about instruction-ID interval credit. *)
Theorem abi_encoder_static_child_site_guard:
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  emit_op ADD [dst;Lit (n2w offset)] st = (head,prepared) /\
  abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A ==>
  abi_decoder_emitted_sites prepared.cs_next_id en.cs_next_id prepared en SUBSET A
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`G` |-> `\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A`]
    (SPEC_ALL abi_encoder_static_child_guard))) >>
  asm_rewrite_tac [abi_encoder_hereditary_guard_sites] >>
  metis_tac []
QED

Theorem abi_encoder_dynamic_child_site_guard:
  compile_abi_encode_child dst src ei T offset dp st = (out,en) /\
  abi_encode_child_prefix dst offset dp st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND (SND ops)) src ei prepared = (len,child_end) /\
  abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A ==>
  abi_decoder_emitted_sites prepared.cs_next_id child_end.cs_next_id prepared child_end SUBSET A
Proof
  strip_tac >>
  irule (BETA_RULE (Q.INST [`G` |-> `\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A`]
    (SPEC_ALL abi_encoder_dynamic_child_guard))) >>
  asm_rewrite_tac [abi_encoder_hereditary_guard_sites] >>
  metis_tac []
QED
