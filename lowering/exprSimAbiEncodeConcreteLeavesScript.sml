Theory exprSimAbiEncodeConcreteLeaves
Ancestors
  abiEncoderWindowLeaves abiEncoderWindowContract abiEncoderLeaves abiEncoderWrites
  abiEncoderReentryLeaves moduleLoweringProps abiEncoderMemory
  abiEncoder abiEncoderOpenInput abiEncoderInput contractABI valueEncoding
  abiEncoderPrimitiveEffect abiEncoderExtendSim abiEncoderWindow
  abiEncoderRegisteredEffect valueEncodingProofs valueEncodingProps
  emitHelperProps exprLoweringProps localPtrsProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list
  abiEncoderWindowLookup abiEncoderWindowBytes abiEncoderWindowSequence
  abiEncoderBytes abiEncoderRounding
  valueEncodingDefs

Theorem abi_encode_copy_concrete:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiCopy sz) at av sb cap d s ==>
  ?r. run_inst_seq (emitted_insts st st') s = OK r /\
      window_strong_result ctx func st st' out at av d s
        (r with vs_inst_idx := LENGTH st'.cs_current_insts) /\
      (!x. ~not_fresh_at st' x ==>
        lookup_var x (r with vs_inst_idx := LENGTH st'.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
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
  qexists_tac `mcopy d sb sz s` >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `sb`, `n` |-> `sz`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_word_concrete:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src AbiPrimWord at av sb cap d s ==>
  ?r. run_inst_seq (emitted_insts st st') s = OK r /\
      window_strong_result ctx func st st' out at av d s
        (r with vs_inst_idx := LENGTH st'.cs_current_insts) /\
      (!x. ~not_fresh_at st' x ==>
        lookup_var x (r with vs_inst_idx := LENGTH st'.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at st') i.inst_outputs) (emitted_insts st st')` by
    metis_tac[window_word_output_bounds] >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >> pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  fs[abi_encoder_window_word_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = 32` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `sb < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  `!x. dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_word_run >> strip_tac >>
  `abi_encoder_extend_sim ctx func s
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
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
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (drule abi_window_seq_high_vars >>
      disch_then (qspec_then `st'` mp_tac) >> simp[lookup_var_def]) >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `w` |-> `mload sb s`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_word_state_resources) >>
  simp[] >> strip_tac >>
  gvs[abi_encoder_word_window, mstore_mem_word_at_same, update_var_def,
    GSYM mem_word_at_eq_mload, mstore_def, write_memory_with_expansion_def] >>
  asm "sizes" ACCEPT_TAC
QED

Theorem abi_encode_empty_concrete:
  compile_abi_encode_to_buf dst src (AbiComplex []) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiComplex []) at av sb cap d s ==>
  ?r. run_inst_seq (emitted_insts st st') s = OK r /\
      window_strong_result ctx func st st' out at av d s
        (r with vs_inst_idx := LENGTH st'.cs_current_insts) /\
      (!x. ~not_fresh_at st' x ==>
        lookup_var x (r with vs_inst_idx := LENGTH st'.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >> pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  `enc at av = []` by
    (fs[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def, enc_def, LET_THM, REV_DEF]) >>
  `s with vs_inst_idx := LENGTH st.cs_current_insts = s` by
    (qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  qexists_tac `s` >>
  simp[emitted_insts_def, run_inst_seq_def, window_strong_result_def,
    abi_encoder_window_result_def, mem_bytes_at_def, eval_operand_def,
    abi_encoder_registered_effect_refl, abi_encoder_extend_sim_refl,
    abi_encoder_extend_sim_sim, window_alloca_growth_def] >>
  (conj_tac >- metis_tac[optionTheory.NOT_SOME_NONE]) >>
  asm "sizes" ACCEPT_TAC
QED

(* Retain the raw bytestring endpoint before observer lifting. *)
Theorem abi_encode_bytes_concrete:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiBytestring maxlen) at av sb cap d s ==>
  ?r. run_inst_seq (emitted_insts st st') s = OK r /\
      window_strong_result ctx func st st' out at av d s
        (r with vs_inst_idx := LENGTH st'.cs_current_insts) /\
      (!x. ~not_fresh_at st' x ==>
        lookup_var x (r with vs_inst_idx := LENGTH st'.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
             EVERY (not_fresh_at st') i.inst_outputs) (emitted_insts st st')` by
    metis_tac[window_bytes_output_bounds] >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >> pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
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
   32+LENGTH bs < dimword (:256)` by decide_tac >>
  `mload sb s = n2w (LENGTH bs)` by metis_tac[mem_word_at_eq_mload] >>
  `!x. dst = Var x \/ src = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_bytes_sequence >> strip_tac >>
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
  `abi_encoder_extend_sim ctx func s
    (actual with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule window_seq_extend_sim >> simp[] >> qexists_tac `st` >> simp[]) >>
  (qexists_tac `actual` >> conj_tac >- gvs[window_seq_def] >>
  reverse conj_tac
  >- (`run_inst_seq (emitted_insts st st') s = OK actual` by gvs[window_seq_def] >>
      drule abi_window_seq_high_vars >>
      disch_then (qspec_then `st'` mp_tac) >> simp[lookup_var_def]) >>
  `alloca_inv actual` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room ctx func actual` by
    (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  `st'.cs_current_bb = st.cs_current_bb` by metis_tac[window_seq_def] >>
  qpat_x_assum `actual.vs_memory = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `window_strong_result _ _ _ _ _ _ _ _ _ final` >>
  `final.vs_allocas = s.vs_allocas /\ final.vs_alloca_next = s.vs_alloca_next` by
    simp[Abbr `final`] >>
  `alloca_inv final` by (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  `alloca_room ctx func final` by
    (irule alloca_room_fields >> qexists_tac `s` >> simp[Abbr `final`]) >>
  `eval_operand out final = eval_operand out actual` by
    (Cases_on `out` >> simp_tac (srw_ss()) [eval_operand_def, lookup_var_def, Abbr `final`]) >>
  `!x. lookup_var x final = lookup_var x actual` by simp[lookup_var_def, Abbr `final`] >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
     [(d,LENGTH (enc at (BytesV bs)))] s final` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `actual` >>
     simp[Abbr `final`, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st') [(d,LENGTH (enc at (BytesV bs)))] s final` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`,
       `[(d,LENGTH (enc at (BytesV bs))) ]`] >> simp[window_alloca_sites_subset]) >>
  `mem_bytes_at d (LENGTH (enc at (BytesV bs))) final.vs_memory = enc at (BytesV bs)` by
    (qpat_assum `mem_bytes_at _ _ actual.vs_memory = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `final`]) >>
  `window_alloca_growth s final` by
    (simp[window_alloca_growth_def] >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x final = SOME w` by
    metis_tac[window_seq_def] >>
  `~final.vs_halted /\ final.vs_current_bb = st'.cs_current_bb /\
   final.vs_inst_idx = LENGTH st'.cs_current_insts` by simp[Abbr `final`] >>
  `abi_decode_sim ctx func s final` by metis_tac[abi_encoder_extend_sim_sim] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  asm_rewrite_tac[] >> (conj_tac >- asm "sizes" ACCEPT_TAC) >>
  simp[Abbr `final`] >> metis_tac[window_seq_labels])
QED
