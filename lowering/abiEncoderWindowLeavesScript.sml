(* Actual-window leaf semantics, without a fresh-variable-map precondition. *)
Theory abiEncoderWindowLeaves
Ancestors
  abiEncoderWindowContract abiEncoderLeaves abiEncoderWrites
  abiEncoderReentryLeaves moduleLoweringProps abiEncoderMemory
  abiEncoder abiEncoderOpenInput abiEncoderInput contractABI valueEncoding
  abiEncoderPrimitiveEffect abiEncoderExtendSim abiEncoderWindow
  abiEncoderRegisteredEffect valueEncodingProofs valueEncodingProps
  emitHelperProps exprLoweringProps localPtrsProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list

Theorem window_emit_copy_run:
  emit_void MCOPY [dst;src;len] st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand len s = SOME (n2w n) /\
  d < dimword (:256) /\ sb < dimword (:256) /\ n < dimword (:256) ==>
  run_inst_seq (emitted_insts st st') s = OK (mcopy d sb n s) /\
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, Once step_inst_base_def,
    mk_inst_def, w2n_n2w] >>
  gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem window_copy_state_resources:
  alloca_inv s /\ alloca_room ctx func s ==>
  alloca_inv ((mcopy d sb n s) with vs_inst_idx := ix) /\
  alloca_room ctx func ((mcopy d sb n s) with vs_inst_idx := ix) /\
  (!x. lookup_var x ((mcopy d sb n s) with vs_inst_idx := ix) = lookup_var x s) /\
  (mcopy d sb n s).vs_current_bb = s.vs_current_bb /\
  window_alloca_growth s ((mcopy d sb n s) with vs_inst_idx := ix)
Proof
  strip_tac >> conj_tac
  >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def,
    window_alloca_growth_def] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem window_copy_contract:
  window_strong_contract (AbiCopy sz)
Proof
  simp_tac bool_ss [window_strong_contract_def] >> rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
  drule abi_encode_copy_code >> strip_tac >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  fs[abi_encoder_window_copy_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = sz` by
    metis_tac[LENGTH_mem_bytes_at_proof] >>
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
  qexists_tac `(mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `sb`, `n` |-> `sz`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[venomExecSemanticsTheory.mcopy_def,
    venomStateTheory.write_memory_with_expansion_def]
QED

Theorem window_word_run:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\
  sb < dimword (:256) /\ d < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
    st'.cs_current_bb = st.cs_current_bb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    t = mstore d (mload sb s)
      (update_var (STRING #"%" (toString st.cs_next_var)) (mload sb s) s) /\
    out = Lit 32w
Proof
  strip_tac >> drule abi_encode_word_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `inst_extends st loaded_st` by metis_tac[inst_extends_emit_op] >>
  `inst_extends loaded_st st'` by metis_tac[inst_extends_emit_void] >>
  `eval_operand dst (update_var (STRING #"%" (toString st.cs_next_var))
       (mload sb s) s) = SOME (n2w d)` by
    (Cases_on `dst` >> gvs[eval_operand_def] >>
     metis_tac[lookup_var_update_not_fresh, arithmeticTheory.LESS_EQ_REFL]) >>
  `emitted_insts st st' = emitted_insts st loaded_st ++ emitted_insts loaded_st st'` by
    metis_tac[emitted_insts_append] >>
  gvs[] >> simp[run_inst_seq_def, Once step_inst_base_def, w2n_n2w,
    eval_operand_def, lookup_var_update_var] >>
  simp[Once step_inst_base_def, w2n_n2w, eval_operand_def,
    lookup_var_update_var, mk_inst_def, is_terminator_def,
    exec_read1_def, exec_write2_def, eval_operands_def] >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  metis_tac[inst_extends_trans]
QED

Theorem window_word_state_resources:
  alloca_inv s /\ alloca_room ctx func s ==>
  alloca_inv ((mstore d w (update_var (STRING #"%" (toString st.cs_next_var)) w s))
    with vs_inst_idx := ix) /\
  alloca_room ctx func ((mstore d w (update_var (STRING #"%" (toString st.cs_next_var)) w s))
    with vs_inst_idx := ix) /\
  (!x. not_fresh_at st x ==>
    lookup_var x ((mstore d w (update_var (STRING #"%" (toString st.cs_next_var)) w s))
      with vs_inst_idx := ix) = lookup_var x s) /\
  window_alloca_growth s ((mstore d w (update_var (STRING #"%" (toString st.cs_next_var)) w s))
    with vs_inst_idx := ix)
Proof
  strip_tac >> conj_tac
  >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[update_var_def]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >> simp[update_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `lookup_var x (update_var (STRING #"%" (toString st.cs_next_var)) w s) = lookup_var x s` by
        (irule lookup_var_update_not_fresh >> qexists_tac `st` >> simp[]) >>
      fs[lookup_var_def, mstore_def, write_memory_with_expansion_def]) >>
  simp[window_alloca_growth_def, update_var_def, mstore_def, write_memory_with_expansion_def] >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem window_word_contract:
  window_strong_contract AbiPrimWord
Proof
  simp_tac bool_ss [window_strong_contract_def] >> rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
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
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `w` |-> `mload sb s`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_word_state_resources) >>
  simp[] >> strip_tac >>
  gvs[abi_encoder_word_window, mstore_mem_word_at_same, update_var_def,
    GSYM mem_word_at_eq_mload, mstore_def, write_memory_with_expansion_def] >>
  asm "sizes" ACCEPT_TAC
QED

Theorem window_empty_contract:
  window_strong_contract (AbiComplex [])
Proof
  simp_tac bool_ss [window_strong_contract_def] >> rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  `enc at av = []` by
    (fs[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def, enc_def, LET_THM, REV_DEF]) >>
  qexists_tac `s` >>
  simp[window_strong_result_def, abi_encoder_window_result_def,
    mem_bytes_at_def, eval_operand_def, abi_encoder_registered_effect_refl,
    abi_encoder_extend_sim_refl, abi_encoder_extend_sim_sim,
    window_alloca_growth_def] >>
  (conj_tac >- metis_tac[optionTheory.NOT_SOME_NONE]) >>
  asm "sizes" ACCEPT_TAC
QED

Theorem window_emit_load_run:
  emit_op MLOAD [ptr_op] st = (out,st') /\
  eval_operand ptr_op s = SOME (n2w p) /\ p < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (mload p s) /\
    inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
    st'.cs_current_bb = st.cs_current_bb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    t = update_var (STRING #"%" (toString st.cs_next_var)) (mload p s) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  gvs[] >> simp[run_inst_seq_def, Once step_inst_base_def,
    exec_read1_def, mk_inst_def, eval_operands_def, w2n_n2w,
    eval_operand_def, lookup_var_update_var, is_terminator_def] >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem window_emit_store_run:
  emit_void MSTORE [ptr_op;value] st = ((),st') /\
  eval_operand ptr_op s = SOME (n2w p) /\ eval_operand value s = SOME w /\
  p < dimword (:256) ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore p w s) /\
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  gvs[] >> simp[run_inst_seq_def, Once step_inst_base_def,
    exec_write2_def, mk_inst_def, eval_operands_def, w2n_n2w,
    is_terminator_def] >>
  gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]
QED
