(* Same-witness safe primitive window encoder contracts. *)
Theory abiEncoderWindowLeavesMem
Ancestors
  abiEncoderWindowLeaves abiEncoderWindowContract abiEncoderWindowComplex
  abiEncoderWindowPhase abiEncoderWindowBytes abiEncoderRounding abiEncoderBytes
  abiEncoderWindowBytesMem abiEncoderWindowSequence windowSequenceMem fragExecMem instMemFrontier allocaFootprint
  abiEncoderLeaves abiEncoderWrites abiEncoderReentryLeaves moduleLoweringProps
  abiEncoderMemory abiEncoder abiEncoderOpenInput abiEncoderInput contractABI valueEncoding
  abiEncoderPrimitiveEffect abiEncoderExtendSim abiEncoderWindow abiEncoderRegisteredEffect
  valueEncodingProofs valueEncodingProps emitHelperProps exprLoweringProps localPtrsProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list arithmetic

Theorem window_copy_contract_mem:
  !dst src st out st' ctx func s at av sb cap d.
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiCopy sz) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t
Proof
  rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >> pop_assum (mk_asm "sizes") >>
  drule abi_encode_copy_code >> strip_tac >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  fs[abi_encoder_window_copy_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = sz` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w sz)) s = SOME (n2w sz)` by simp[eval_operand_def] >>
  drule_all window_emit_copy_run >> strip_tac >>
  `abi_encoder_extend_sim ctx func s
    ((mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
    [(d,sz)] s ((mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `mcopy d sb sz s` >>
     simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st') [(d,sz)] s
    ((mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`, `[(d,sz)]`] >>
     simp[window_alloca_sites_subset]) >>
  `window_seq st st' s (mcopy d sb sz s)` by
    (simp[window_seq_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
     metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (drule emit_mcopy_mem_ok >> disch_then irule >> simp[] >> decide_tac) >>
  `mem_cont_sim ctx func s ((mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  qexists_tac `(mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  asm_rewrite_tac[] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `sb`, `n` |-> `sz`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem window_word_mem_checks[local]:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  sb+32 <= s.vs_alloca_next /\ d+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >> drule abi_encode_word_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `inst_extends st loaded_st /\ inst_extends loaded_st en` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts st en = emitted_insts st loaded_st ++ emitted_insts loaded_st en` by
    metis_tac[emitted_insts_append] >>
  `eval_operand dst (update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s) = SOME (n2w d)` by
    (Cases_on `dst` >> gvs[eval_operand_def] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL]) >>
  `run_inst_seq_mem_ok (emitted_insts st loaded_st) s` by
    (drule emit_mload_mem_ok >> disch_then irule >> simp[]) >>
  pure_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
  asm_rewrite_tac[] >> reverse conj_tac >- gvs[] >> rpt strip_tac >>
  `s' = update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s` by
    (qpat_x_assum `run_inst_seq _ _ = OK s'` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_read1_def, eval_operands_def, w2n_n2w]) >>
  gvs[] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
    memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
  gvs[update_var_def]
QED

Theorem window_word_contract_mem:
  !dst src st out st' ctx func s at av sb cap d.
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src AbiPrimWord at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t
Proof
  rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >> pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  fs[abi_encoder_window_word_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = 32` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ sb+32 <= s.vs_alloca_next /\
   d+32 <= s.vs_alloca_next` by decide_tac >>
  `!x. dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_word_run >> strip_tac >>
  `window_seq st st' s t` by
    (simp[window_seq_def] >> conj_tac
     >- metis_tac[ci_mono_compile_abi_encode, ci_mono_def, pairTheory.SND] >>
     rpt strip_tac >> simp[mstore_def, write_memory_with_expansion_def] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by metis_tac[window_word_mem_checks] >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[window_seq_mem_cont] >>
  `abi_encoder_extend_sim ctx func s
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[window_seq_extend_sim] >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
    [(d,32)] s (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `t` >>
     (conj_tac >-
       (irule abi_encoder_registered_effect_trans >>
        qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s` >>
        simp[abi_encoder_registered_update_var, abi_encoder_output_store])) >>
     simp[abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st') [(d,32)] s
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`, `[(d,32)]`] >>
     simp[window_alloca_sites_subset]) >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `w` |-> `mload sb s`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_word_state_resources) >>
  simp[] >> strip_tac >>
  gvs[abi_encoder_word_window, mstore_mem_word_at_same, update_var_def,
    GSYM mem_word_at_eq_mload, mstore_def, write_memory_with_expansion_def] >>
  conj_tac >- metis_tac[abi_encoder_extend_sim_sim] >>
  asm "sizes" ACCEPT_TAC
QED

Theorem window_leaf_sequence_result[local]:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  window_seq st en s raw /\
  mem_bytes_at d (LENGTH (enc at av)) raw.vs_memory = enc at av /\
  eval_operand out raw = SOME (n2w (LENGTH (enc at av))) /\
  abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s raw /\
  raw.vs_allocas = s.vs_allocas /\ raw.vs_alloca_next = s.vs_alloca_next /\
  raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb ==>
  window_strong_result ctx func st en out at av d s
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  strip_tac >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    metis_tac[window_pre_sites] >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `alloca_inv raw` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room ctx func raw` by
    (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  `window_alloca_growth s raw` by
    (simp[window_alloca_growth_def] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_seq_phase >> simp[]) >>
  irule window_complex_phase_result >> simp[] >>
  Cases_on `out` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem window_bytes_contract_mem:
  !dst src st out st' ctx func s at av sb cap d.
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiBytestring maxlen) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  qpat_assum `abi_encoder_window_input _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_bytes_iff]) >>
  qpat_x_assum `av = BytesV _` SUBST_ALL_TAC >>
  `LENGTH (enc at (BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_ceil32_bounds] >>
  `sb < dimword (:256) /\ LENGTH bs+31 < dimword (:256) /\
   d+contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
   32+LENGTH bs < dimword (:256) /\ sb+32+LENGTH bs <= s.vs_alloca_next /\
   d+32+contractABI$ceil32 (LENGTH bs) <= s.vs_alloca_next /\
   sb+32+LENGTH bs < dimword (:256) /\
   d+32+contractABI$ceil32 (LENGTH bs) < dimword (:256)` by decide_tac >>
  `mload sb s = n2w (LENGTH bs)` by metis_tac[mem_word_at_eq_mload] >>
  `!x. dst = Var x \/ src = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_bytes_sequence_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `window_seq st st' s actual` >>
  `sb + cap <= d \/ d + LENGTH (enc at (BytesV bs)) <= sb` by
    (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     pure_asm_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at d (LENGTH (enc at (BytesV bs))) actual.vs_memory = enc at (BytesV bs)` by
    (qpat_assum `actual.vs_memory = _` (fn th => rewrite_tac[th]) >>
     irule window_bytes_input_memory >> qexistsl_tac [`cap`, `maxlen`] >> asm_rewrite_tac[]) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
     [(d,LENGTH (enc at (BytesV bs)))] s actual` by
    (asm_rewrite_tac[] >> irule window_bytes_effect >> simp[] >>
     qexistsl_tac [`LENGTH bs`, `sb`] >> simp[]) >>
  qexists_tac `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  asm_rewrite_tac[] >> metis_tac[window_leaf_sequence_result]
QED
