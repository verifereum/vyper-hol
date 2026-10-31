(* Normalize an arbitrary public entry environment before the shared runner. *)
Theory abiEncoderEntry
Ancestors
  abiEncoderResourceAdapter abiEncoderCounters abiDecoderReentry emitHelperProps
  compileEnv fragExec list

Theorem abi_encoder_prune_limit_fresh:
  compile_abi_encode_to_buf dst src ei st = (out,st') ==>
  fresh_vars_wrt st' (abi_decoder_prune_vars st.cs_next_var s)
Proof
  strip_tac >> drule abi_encoder_counters >> strip_tac >>
  irule fresh_vars_wrt_mono >> qexists_tac `st` >>
  simp[abi_decoder_prune_fresh, arithmeticTheory.GREATER_EQ]
QED

Theorem abi_encoder_pruned_entry:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  enc_pre st st' [dst;src] lo top tv v sb outs s /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
  fresh_vars_wrt st' (abi_decoder_prune_vars st.cs_next_var s) /\
  enc_pre st st' [dst;src] lo top tv v sb outs
    (abi_decoder_prune_vars st.cs_next_var s) /\
  eval_operand dst (abi_decoder_prune_vars st.cs_next_var s) = SOME dw /\
  eval_operand src (abi_decoder_prune_vars st.cs_next_var s) = SOME sw /\
  (abi_decoder_prune_vars st.cs_next_var s).vs_memory = s.vs_memory /\
  abi_decoder_budget st.cs_next_id st'.cs_next_id lo (top-lo)
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  strip_tac >>
  `enc_pre st st' [dst;src] lo top tv v sb outs
    (abi_decoder_prune_vars st.cs_next_var s)` by
    simp[abi_encoder_prune_pre] >>
  conj_tac >- (drule abi_encoder_prune_limit_fresh >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `enc_pre _ _ _ _ _ _ _ _ _ (abi_decoder_prune_vars _ _)` kall_tac >>
  conj_tac
  >- (drule_at (Pos hd) abi_encoder_pre_prune_eval >> simp[]) >>
  conj_tac
  >- (drule_at (Pos hd) abi_encoder_pre_prune_eval >> simp[]) >>
  conj_tac >- simp[abi_decoder_prune_vars_def] >>
  irule abi_encoder_scratch_budget >>
  fs[abiEncoderPropsTheory.enc_pre_def, abi_encoder_prune_scratch]
QED
