(* History-free, modular source addressing for a recursive array child. *)
Theory calldataArrayModularSetup
Ancestors
  calldataDynStep decoderArraySetupPtr calldataSourceCorrespondence
  entryDecoderSetupEndpoint entryDecoderStateFrame abiDecoderCoherence
  abiDecoderDynamicLoopSetup abiDecoderLoopSetup abiDecoderContract
  abiDecoderReentry abiDecoderArraySetupInputs abiDecoderIndexedAddress
  loweringStateRelDefs compileEnv emitHelper emitHelperProps
  fragGasOriginPtr fragExecPtr ptrDiscipline bodyPtrDefs venomMemDefs
  valueEncodingProps valueEncodingDefs valueEncoding abiDecoderFrame
  venomState venomExecSemantics words arithmetic list finite_map pred_set
  instIdxIndep exprLoweringProps successfulSequenceEndpoint safeSequence fragExecMem rich_list
  vyperCalldata

Theorem calldata_array_modular_child_setup:
  abi_decoder_coherent ce env sf ty tv /\
  dec_info_needs_offset di = is_abi_dynamic ce.ce_struct_fields ty /\
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD
    (Lit 0w) (Lit 0w) di (tv_abi_size tv) (type_memory_size tv) st = (ops,ready) /\
  lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\
  j < dimword (:256) /\ slot+32 < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ lookup_var root s = SOME (n2w dst) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  not_fresh_at st q /\ not_fresh_at st root /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn q s 32 /\ ptr_covers G tn root s cap /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  32+j*type_memory_size tv+type_memory_size tv <= cap /\
  dst+32+j*type_memory_size tv < dimword (:256) /\
  type_memory_size tv < dimword (:256) /\
  ready.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  alloca_inv s /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts
  ==>
  ?raw a H u child.
    run_inst_seq (emitted_insts st ready) s = OK raw /\
    a = raw with vs_inst_idx := LENGTH ready.cs_current_insts /\
    ~a.vs_halted /\ a.vs_current_bb = ready.cs_current_bb /\
    a.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand (FST ops) a = SOME (n2w j) /\
    eval_operand (FST (SND ops)) a = SOME
      (n2w (cd_member_ptr F s.vs_call_ctx.cc_calldata tv
        (cd_at F sb 32) (j*tv_abi_size tv))) /\
    eval_operand (SND (SND ops)) a =
      SOME (n2w (dst+32+j*type_memory_size tv)) /\
    SND (SND ops) = Var child /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    ptr_covers H u child a (type_memory_size tv) /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    op_taint u (FST (SND ops)) = {} /\ op_prov H (FST (SND ops)) = NONE /\
    fresh_vars_wrt limit a /\ alloca_inv a /\ allocas_from lower a /\
    inst_extends st ready /\ entry_decoder_obs s a /\
    a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
    a.vs_alloca_next = s.vs_alloca_next /\
    a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
    a.vs_logs = s.vs_logs /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_tx_ctx = s.vs_tx_ctx /\ a.vs_block_ctx = s.vs_block_ctx /\
    a.vs_outcomes = s.vs_outcomes /\ a.vs_requests = s.vs_requests /\
    a.vs_pending_deletions = s.vs_pending_deletions /\
    a.vs_data_section = s.vs_data_section /\ a.vs_gas_readings = s.vs_gas_readings /\
    a.vs_labels = s.vs_labels /\ a.vs_fmp = s.vs_fmp /\ a.vs_code = s.vs_code /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op a = eval_operand op s) /\
    (!x. not_fresh_at st x ==> lookup_var x a = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    ((!fuel. mem_safe_run fuel ctx fn a) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn a = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn a ==> mem_safe_run fuel' ctx fn s)) /\
    ((!fuel. ptr_safe_run D lower fuel ctx fn PG H u a) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK a,H,u))
Proof
  strip_tac >>
  `eval_operand (Var q) s = SOME (n2w slot) /\
   eval_operand (Var root) s = SOME (n2w dst) /\
   mload (w2n (n2w slot : bytes32)) s = n2w j` by
    (simp[eval_operand_def, w2n_n2w] >> fs[]) >>
  drule_all calldata_element_setup_reentry >> strip_tac >>
  drule_all calldata_array_element_setup_endpoint_ptr_origin_core >>
  disch_then (qspec_then `ARB` mp_tac) >>
  disch_then (qspec_then `ARB` mp_tac) >>
  disch_then (qspecl_then [`ctx`,`PG`,`ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK raw` >>
  `LENGTH (emitted_insts st ready) + s.vs_inst_idx =
    LENGTH ready.cs_current_insts` by fs[inst_extends_def] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op raw = eval_operand op s` by
    (rpt strip_tac >> drule_all entry_element_setup_total_frame >> simp[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule entry_element_setup_reentry_code >> strip_tac >>
  drule_all entry_decoder_sequence_obs >> strip_tac >>
  drule calldata_element_setup_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st ready) s` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (fs[EVERY_MEM] >> metis_tac[]) >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     qexistsl_tac [`src`, `n2w slot`] >>
     goal_assum (drule_at Any) >> simp[w2n_n2w] >> metis_tac[LESS_EQ]) >>
  mp_tac (Q.INST [`P` |-> `\s:venom_state. T`, `t` |-> `raw`]
    (SPEC_ALL successful_sequence_endpoint)) >>
  asm_simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  drule calldata_coherent_dynamic >> strip_tac >>
  suspend "source_word"
QED

Resume calldata_array_modular_child_setup[source_word]:
  qexistsl_tac [`HG`,`u`] >> conj_tac
  >- (Cases_on `tv_abi_dynamic tv` >>
      simp[cd_member_ptr_def, cd_at_def, calldata_decode_load_word,
           w2n_n2w, MOD_PLUS]) >>
  fs[abi_decoder_address_frame_def, entry_decoder_obs_def,
     fresh_vars_wrt_def, alloca_inv_def, allocas_non_overlapping_def,
     alloca_next_valid_def, allocas_from_def, ptr_covers_def,
     lookup_var_def] >>
  metis_tac[]
QED

Finalise calldata_array_modular_child_setup
