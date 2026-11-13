Theory abiEncodeEmptyCopyEndpoint
Ancestors
  valueEncodingDefs exprSimAbiEncodeEmptySource exprSimAbiEncodeExecFrame
  exprSimAbiEncodeFramedSuffix exprSimAbiEncodeSetupOpen abiBuiltinEncodeSetup abiBuiltinAllocation
  abiEncodeWindowBuiltin abiDecoderContract abiDecoderLoop
  exprSimAbiEncodeExecution exprSimAbiEncodeStateTransport exprSimAbiEncodeWindowRoom
  abiEncoderWindowLeaves abiEncoderWindowContract abiEncoderRegisteredEffect
  abiEncoderExtendSim abiEncoderPrimitiveEffect abiEncoderWindowLookup
  abiEncoderLeaves abiEncoderWindow abiEncoderProps valueEncodingProofs
  exprLoweringProps valueEncoding abiEncoderSourceFootprint
  venomState venomExecSemantics compileEnv list words

Theorem abi_encode_empty_copy_endpoint:
  compile_abi_encode_to_buf dst src (AbiCopy 0) st = (out,st') /\
  abi_encode_empty_window_pre ctx func st st' dst src at av a d s ==>
  window_strong_result ctx func st st' out at av d s
    ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  (!x. ~not_fresh_at st' x ==>
    lookup_var x ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts) = lookup_var x s) /\
  abi_encode_exec_frame func s
    ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts) /\
  ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts).vs_labels = s.vs_labels
Proof
  simp_tac bool_ss [abi_encode_empty_window_pre_def] >> strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    (simp[window_alloca_sites_def] >> metis_tac[]) >>
  pop_assum (mk_asm "sizes") >>
  drule abi_encode_copy_code >> strip_tac >>
  fs[abi_encoder_window_copy_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = 0` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `d < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w 0)) s = SOME (n2w 0)` by simp[eval_operand_def] >>
  `eval_operand src s = SOME (n2w (w2n a))` by simp[] >>
  `w2n a < dimword (:256) /\ 0 < dimword (:256)` by simp[wordsTheory.w2n_lt, wordsTheory.dimword_def] >>
  drule_all window_emit_copy_run >> strip_tac >>
  `abi_encoder_extend_sim ctx func s
    ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
    [(d,0)] s ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `mcopy d (w2n a) 0 s` >>
     simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st') [(d,0)] s
    ((mcopy d (w2n a) 0 s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`, `[(d,0)]`] >>
     simp[window_alloca_sites_subset]) >>
  reverse conj_tac
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `w2n (a:256 word)`, `n` |-> `0`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[venomExecSemanticsTheory.mcopy_def,
    venomStateTheory.write_memory_with_expansion_def]
QED
