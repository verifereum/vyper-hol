(* Assemble the public frame from the shared endpoint's concrete effects. *)
Theory abiEncoderFragmentFrame
Ancestors
  abiEncoderRegisteredFrame abiEncoderResourceAdapter abiEncoderVarRestore
  abiEncoderSharedContract abiScratchEncoderContract abiDecoderAllocation
  abiDecoderVarExtend abiDecoderReentry abiDecoderContract venomState valueEncoding
  abiEncoderProps abiEncoderRegisteredEffect venomMemDefs compileEnv words

Theorem abi_encoder_budget_registered_frame:
  lo <= top /\
  abi_decoder_budget st.cs_next_id st'.cs_next_id lo (top-lo) actual /\
  alloca_inv actual /\
  abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id st'.cs_next_id)
    outs initial actual /\
  (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w) ==>
  enc_frame st st' lo top outs initial actual
Proof
  strip_tac >> irule abi_encoder_registered_effect_frame >>
  asm_rewrite_tac[abi_encoder_fragment_ids] >>
  rewrite_tac[GSYM abi_encoder_fragment_ids] >>
  irule abi_encoder_budget_scratch >> simp[]
QED

Theorem abi_encoder_restored_frame:
  abi_encoder_shared_endpoint (ctx,func) (st,st',out,st')
    (st.cs_next_id,st'.cs_next_id,lo,top-lo) (at,av,d)
    (abi_decoder_prune_vars st.cs_next_var initial) actual /\
  abi_decoder_vars_extend initial.vs_vars actual restored /\
  lo <= top /\ alloca_inv initial ==>
  enc_frame st st' lo top [(d,LENGTH (enc at av))] initial restored
Proof
  strip_tac >>
  `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
      lookup_var x restored = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by
       fs[not_fresh_at_def, abi_decoder_operand_live_def,
          abi_decoder_older_vars_def] >>
     `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
     drule_all abi_encoder_restored_operand >> simp[eval_operand_def]) >>
  drule abi_encoder_vars_extend_fields >>
  simp_tac bool_ss [pairTheory.PAIR_EQ] >> strip_tac >>
  irule abi_encoder_budget_registered_frame >> asm_rewrite_tac[] >>
  `abi_decoder_budget st.cs_next_id st'.cs_next_id lo (top-lo) actual` by
    (drule abi_encoder_shared_endpoint_scratch >> simp[abi_scratch_effect_def]) >>
  `alloca_inv (abi_decoder_prune_vars st.cs_next_var initial)` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     simp[abi_decoder_prune_vars_def, alloca_inv_def,
       alloca_next_valid_def, allocas_non_overlapping_def]) >>
  `alloca_inv actual` by
    (drule_all abi_encoder_shared_endpoint_alloca_inv >> simp[]) >>
  drule abi_encoder_shared_endpoint_registered >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_endpoint _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_vars_extend _ _ _` kall_tac >>
  conj_tac
  >- (qpat_x_assum `alloca_inv actual` mp_tac >>
      simp[alloca_inv_def, alloca_next_valid_def, allocas_non_overlapping_def]) >>
  conj_tac
  >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
      simp[abi_decoder_prune_vars_def, abi_encoder_registered_effect_def] >>
      metis_tac[]) >>
  qpat_x_assum `abi_decoder_budget _ _ _ _ actual` mp_tac >>
  pure_rewrite_tac[abi_decoder_budget_def, abi_decoder_missing_def] >>
  qpat_x_assum `restored.vs_allocas = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `restored.vs_alloca_next = _` (fn th => rewrite_tac[th])
QED
