(* Safety of supplied first-cut executions, independent of their existence. *)
Theory abiEncoderLeafSafety
Ancestors
  abiEncoderPrefixSafety abiEncoderExactWriteProbe abiEncoderObserverCode abiEncoderObserver
  abiDecoderContract abiDecoderReentry fragExec emitHelperProps venomExecSemantics venomState
  finite_map pred_set instIdxIndep valueEncodingProps abiEncoderWrites
  words list arithmetic emitHelper venomInst

Theorem local_prefix_nonterminator_inv:
  local_prefix ctx fn cut s t /\
  (s.vs_current_bb,s.vs_inst_idx) <> cut /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode ==>
  ?middle. step_inst 0 ctx inst s = OK middle /\
    local_prefix ctx fn cut
      (middle with vs_inst_idx := SUC s.vs_inst_idx) t
Proof
  strip_tac >>
  qpat_x_assum `local_prefix _ _ _ _ _` mp_tac >>
  simp[Once local_prefix_cases] >> strip_tac >>
  gvs[abi_observer_step_def] >> metis_tac[]
QED

Theorem local_prefix_at_cut:
  local_prefix ctx fn (s.vs_current_bb,s.vs_inst_idx) s t ==> t = s
Proof
  simp[Once local_prefix_cases, abi_observer_step_def]
QED

Theorem abi_word_prefix_fetch:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  fn_has_code st st' fn ==>
  ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id MLOAD [src]
        [STRING #"%" (toString st.cs_next_var)]) /\
    get_instruction bb (SUC (LENGTH st.cs_current_insts)) =
      SOME (mk_inst (st.cs_next_id+1) MSTORE
        [dst; Var (STRING #"%" (toString st.cs_next_var))] [])
Proof
  strip_tac >> drule abi_word_compiler_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  conj_tac >> first_x_assum (fn th =>
    mp_tac (Q.SPEC `0` th) >> mp_tac (Q.SPEC `1` th)) >> simp[ADD1]
QED

Theorem word_load_step_inv:
  step_inst 0 ctx (mk_inst site MLOAD [src] [tmp]) s = OK middle ==>
  ?w. eval_operand src s = SOME w /\
      middle = update_var tmp (mload (w2n w) s) s
Proof
  simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def,
       exec_read1_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem word_live_destination_update:
  abi_decoder_operand_live next dst ==>
  eval_operand dst (update_var (STRING #"%" (toString next)) w s) =
    eval_operand dst s
Proof
  Cases_on `dst` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, update_var_def, lookup_var_def] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE] >> metis_tac[LESS_EQ_REFL]
QED

Theorem abi_word_prefix_state:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  fn_has_code st st' fn /\ eval_operand dst s = SOME (n2w d) /\
  d+32 < dimword (:256) /\ abi_decoder_operand_live st.cs_next_var dst /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_prefix ctx fn (st'.cs_current_bb,LENGTH st'.cs_current_insts) s t ==>
  ?w. t = (mstore d w (update_var (STRING #"%" (toString st.cs_next_var)) w s)
             with vs_inst_idx := LENGTH st.cs_current_insts + 2)
Proof
  strip_tac >> drule_all abi_word_prefix_fetch >> strip_tac >>
  drule abi_word_compiler_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mk_inst st.cs_next_id MLOAD [src] [tmp]` >>
  `?middle. step_inst 0 ctx (mk_inst st.cs_next_id MLOAD [src] [tmp]) s = OK middle /\
    local_prefix ctx fn (st'.cs_current_bb,LENGTH st'.cs_current_insts)
      (middle with vs_inst_idx := SUC s.vs_inst_idx) t` by
    (irule local_prefix_nonterminator_inv >>
     simp[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  drule word_load_step_inv >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `local_prefix ctx fn cut loaded t` >>
  `loaded.vs_current_bb = st.cs_current_bb /\
   loaded.vs_inst_idx = SUC (LENGTH st.cs_current_insts)` by
    simp[Abbr `loaded`, update_var_def] >>
  `eval_operand dst loaded = SOME (n2w d)` by
    (simp[Abbr `loaded`, eval_op_inst_idx] >>
     unabbrev_all_tac >> simp[word_live_destination_update]) >>
  `eval_operand (Var tmp) loaded = SOME (mload (w2n w) s)` by
    simp[Abbr `loaded`, eval_op_inst_idx, eval_operand_update_var] >>
  `?middle. step_inst 0 ctx (mk_inst (st.cs_next_id+1) MSTORE [dst;Var tmp] []) loaded = OK middle /\
    local_prefix ctx fn cut
      (middle with vs_inst_idx := SUC loaded.vs_inst_idx) t` by
    (irule local_prefix_nonterminator_inv >>
     simp[Abbr `cut`, mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  gvs[step_inst_non_invoke, mk_inst_def, step_inst_base_def, exec_write2_def] >>
  qpat_x_assum `local_prefix _ _ _ _ t` mp_tac >>
  simp[Once local_prefix_cases, abi_observer_step_def, Abbr `cut`,
       Abbr `loaded`, mstore_def, write_memory_with_expansion_def,
       update_var_def, ADD1] >>
  rpt strip_tac >> qexists_tac `mload (w2n w) s` >> simp[]
QED

Theorem abi_word_prefix_exact_writes:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  fn_has_code st st' fn /\ eval_operand dst s = SOME (n2w d) /\
  d+32 < dimword (:256) /\ abi_decoder_operand_live st.cs_next_var dst /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_prefix ctx fn (st'.cs_current_bb,LENGTH st'.cs_current_insts) s t ==>
  encoder_exact_writes (abi_decoder_ids st.cs_next_id st'.cs_next_id) d 32 s t
Proof
  strip_tac >> drule_all abi_word_prefix_state >> strip_tac >>
  `!p w v. (mstore p w (update_var (STRING #"%" (toString st.cs_next_var)) v s)).vs_memory =
             (mstore p w s).vs_memory` by
    simp[mstore_def, write_memory_with_expansion_def, update_var_def] >>
  gvs[encoder_exact_writes_def] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]
QED

Theorem abi_word_prefix_allocations:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  fn_has_code st st' fn /\ eval_operand dst s = SOME (n2w d) /\
  d+32 < dimword (:256) /\ abi_decoder_operand_live st.cs_next_var dst /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_prefix ctx fn (st'.cs_current_bb,LENGTH st'.cs_current_insts) s t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_word_prefix_state >> strip_tac >>
  gvs[update_var_def]
QED

Theorem abi_word_prefix_public_state:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  fn_has_code st st' fn /\ eval_operand dst s = SOME (n2w d) /\
  d+32 < dimword (:256) /\ abi_decoder_operand_live st.cs_next_var dst /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  local_prefix ctx fn (st'.cs_current_bb,LENGTH st'.cs_current_insts) s t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests
Proof
  strip_tac >> drule_all abi_word_prefix_state >> strip_tac >>
  gvs[mstore_def, write_memory_with_expansion_def, update_var_def]
QED
