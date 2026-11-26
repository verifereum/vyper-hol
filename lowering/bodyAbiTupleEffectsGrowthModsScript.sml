Theory bodyAbiTupleEffectsGrowthMods
Ancestors
  bodyAbiTupleBufferStateMods abiEncoderWindowContract abiEncoderRegisteredEffect
  exprSimAbiEncodeExecFrame exprLoweringProps

Theorem abi_tuple_effects_growth_trans_mods:
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu c z Gz tz ==>
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    c z Gz tz e q Ge tq ==>
  ci_mono a e /\ window_alloca_growth u q /\ abi_encode_exec_frame func u q
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  disch_then (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  conj_tac >- (irule ci_mono_trans >> qexists_tac `c` >> simp[]) >>
  conj_tac
  >- (irule window_alloca_growth_trans >> qexists_tac `z` >> simp[] >>
      rpt strip_tac >>
      irule abi_encoder_registered_effect_allocated >> simp[] >> metis_tac[]) >>
  irule abi_encode_exec_frame_trans >> qexists_tac `z` >> simp[]
QED
