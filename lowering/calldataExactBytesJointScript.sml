(* Exact bytes/string decoding with one source, runtime and ghost endpoint. *)
Theory calldataExactBytesJoint
Ancestors
  calldataBytesSourceExact defaultBytesDecodeExec calldataDecodePtr
  calldataFiniteTransport exprPtrCleanBufferPost abiDecoderFrameCompose
  calldataBytesRejectOrigin calldataBytesFiniteFrame fragGasOriginPtrExec
  abiCallerAllocation abiDecoderFrame
  abiDecoderCoherence abiDecoderReentry abiDecoderContract abiDecoderBytes
  abiDecoderBytesTyped abiDecoderString calldataSourceCorrespondence
  fragExecMem fragGasOriginPtr compileEnv loweringStateRelDefs
  venomExecSemantics venomState valueEncodingDefs valueEncoding
  vyperCalldata vyperValue vyperTyping exprLowering exprLoweringProps
  words arithmetic list finite_map

Theorem calldata_exact_bytes_shape[local]:
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty ==>
  ?maxn. type_to_abi_dec_info sf ce ty = DecBytestring maxn /\
    type_memory_size tv = abi_decode_bytes_copy_size maxn /\
    (tv = BaseTV (BytesT (Dynamic maxn)) \/ tv = BaseTV (StringT maxn))
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
  qpat_x_assum `is_bytestring_type ty` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  rpt strip_tac >> gvs[evaluate_type_def, is_bytestring_type_def, AllCaseEqs()] >>
  simp[type_to_abi_dec_info_def, type_memory_bytes_def, type_memory_size_def,
    abi_decode_bytes_copy_size_def, vfmConstantsTheory.word_size_def]
QED

Theorem calldata_exact_bytes_accepted_origin[local]:
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty /\
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  ptr_covers G tn child initial (type_memory_size tv) /\ op_taint tn src = {} /\
  d+type_memory_size tv <= initial.vs_alloca_next /\
  d+type_memory_size tv < dimword (:256) /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?v H u.
    run_inst_seq (emitted_insts st last) initial =
      OK (v with vs_inst_idx := initial.vs_inst_idx) /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!mem. mem_agree_outside u.t_mem v.vs_memory mem ==>
      val_in_memory tv x d mem) /\
    v.vs_allocas = initial.vs_allocas /\
    v.vs_alloca_next = initial.vs_alloca_next /\
    ptr_covers H u child v (type_memory_size tv) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!name. not_fresh_at st name ==>
      FLOOKUP H name = FLOOKUP G name /\
      op_taint u (Var name) = op_taint tn (Var name)) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))
Proof
  strip_tac >> drule_all calldata_exact_bytes_shape >> strip_tac >>
  `maxn < dimword (:256)` by
    (irule calldataBytesLiveTheory.abi_decode_bytes_extent_capacity_bound >> qexists `d` >> simp[]) >>
  `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn` by
    (qpat_x_assum `cd_decode F _ _ _ = SOME x` mp_tac >>
     gvs[] >>
     simp[cd_decode_def, GSYM calldata_decode_load_word, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  drule_all default_bytes_decode_exact_sequence >> strip_tac >>
  `not_fresh_at st child /\ (!q. src = Var q ==> not_fresh_at st q)` by
    (gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  `type_memory_size tv = 32 + 32 * ((maxn+31) DIV 32)` by
    simp[abi_decode_bytes_copy_size_def] >>
  `type_memory_size tv < dimword (:256) /\ d < dimword (:256)` by
    decide_tac >>
  `abi_decode_load CALLDATALOAD p initial =
    n2w (w2n (abi_decode_load CALLDATALOAD p initial))` by simp[] >>
  `compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) st = ((),last)` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp initial` by simp[] >>
  drule_all calldata_bytestring_overwrite_endpoint_core_uniform_origin_sequence >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t = s' with vs_inst_idx := initial.vs_inst_idx` by metis_tac[exec_result_11] >>
  `val_in_memory tv x d s'.vs_memory` by fs[] >>
  gvs[wordsTheory.w2n_n2w] >>
  qexistsl [`s'`, `G'`, `tn'`] >> simp[] >>
  rpt strip_tac >> irule clean_window_value_robust >>
  (conj_tac >- fs[]) >>
  qexistsl [`tn'.t_mem`, `s'.vs_memory`, `abi_decode_bytes_copy_size maxn`] >>
  fs[wordsTheory.w2n_n2w]
QED

Theorem calldata_exact_bytes_joint_limit:
  !ce env sf ty tv
   st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG.
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty /\
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
  d+type_memory_size tv < dimword (:256) /\
  ptr_covers G tn child initial (type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit initial /\ allocas_from lower initial /\
  lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
   ?z H u. z.vs_returndata = [] /\
     (?fuel. run_from fuel ctx fn initial = Abort Revert_abort z /\
       mem_safe_run fuel ctx fn initial) /\
     (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
       (initial,G,tn) [] (Abort Revert_abort z,H,u))) \/
  ?v x sc H u.
    cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!mem. mem_agree_outside u.t_mem v.vs_memory mem ==> val_in_memory tv x d mem) /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    v.vs_accounts = initial.vs_accounts /\ v.vs_transient = initial.vs_transient /\
    v.vs_logs = initial.vs_logs /\ v.vs_outcomes = initial.vs_outcomes /\
    v.vs_requests = initial.vs_requests /\
    v.vs_pending_deletions = initial.vs_pending_deletions /\
    v.vs_tx_ctx = initial.vs_tx_ctx /\ v.vs_block_ctx = initial.vs_block_ctx /\
    v.vs_fmp = initial.vs_fmp /\ v.vs_gas_readings = initial.vs_gas_readings /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size tv)::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    fresh_vars_wrt limit v /\ ptr_covers H u child v (type_memory_size tv) /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_exact_bytes_shape >>
  disch_then (qx_choose_then `maxn` (map_every assume_tac o CONJUNCTS)) >>
  `d+type_memory_size tv <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `maxn < dimword (:256)` by
    (irule calldataBytesLiveTheory.abi_decode_bytes_extent_capacity_bound >>
     qexists `d` >> fs[]) >>
  `compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) st = ((),last)` by metis_tac[] >>
  Cases_on `cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p)`
  >- suspend "rejected" >>
  rename1 `cd_decode F _ _ _ = SOME x` >>
  drule_all calldata_exact_bytes_accepted_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "accepted"
QED

Resume calldata_exact_bytes_joint_limit[rejected]:
  `maxn < w2n (abi_decode_load CALLDATALOAD p initial)` by
    (qpat_x_assum `cd_decode F _ _ _ = NONE` mp_tac >>
     qpat_assum `tv = _ \/ tv = _` strip_assume_tac >>
     pop_assum SUBST1_TAC >>
     rpt (pop_assum kall_tac) >>
     simp[cd_decode_def, GSYM calldata_decode_load_word]) >>
  drule_all calldata_bytes_rejected_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  disj1_tac >> simp[] >> qexistsl [`z`,`H`,`u`] >> simp[] >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
    (qspecl_then [`ARB`,`{}`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_exec) >>
  simp_tac (srw_ss()) [fragExecTheory.exit_result_def] >> metis_tac[]
QED

Resume calldata_exact_bytes_joint_limit[accepted]:
  `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn` by
    (qpat_x_assum `cd_decode F _ _ _ = SOME x` mp_tac >>
     qpat_assum `tv = _ \/ tv = _` strip_assume_tac >>
     pop_assum SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     simp[cd_decode_def, GSYM calldata_decode_load_word, AllCaseEqs()]) >>
  `not_fresh_at st child /\ (!q. src = Var q ==> not_fresh_at st q)` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`abi_decoder_operand_live _ src`, `abi_decoder_operand_live _ (Var child)`] >>
     rpt (pop_assum kall_tac) >>
     Cases_on `src` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `type_memory_size tv = 32 + 32 * ((maxn+31) DIV 32)` by
    (qpat_assum `type_memory_size tv = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[abi_decode_bytes_copy_size_def]) >>
  `type_memory_size tv < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  `abi_decode_load CALLDATALOAD p initial =
    n2w (w2n (abi_decode_load CALLDATALOAD p initial))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp initial` by simp[] >>
  drule_all calldata_bytestring_overwrite_endpoint_core_uniform_origin_sequence >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `v with vs_inst_idx := initial.vs_inst_idx =
   s' with vs_inst_idx := initial.vs_inst_idx` by metis_tac[exec_result_11] >>
  `s' = v` by
    (qpat_x_assum `(v with vs_inst_idx := _) = _`
       (mp_tac o Q.AP_TERM `\s. s with vs_inst_idx := LENGTH last.cs_current_insts`) >>
     qpat_assum `v.vs_inst_idx = _` mp_tac >>
     qpat_assum `s'.vs_inst_idx = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >> fs[venom_state_component_equality]) >>
  pop_assum SUBST_ALL_TAC >>
  `w2n (n2w d:bytes32) = d` by
    (qpat_assum `d < dimword (:256)` mp_tac >> rpt (pop_assum kall_tac) >> simp[]) >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
    (initial,G,tn) [] (OK v,G',tn')` by
    (qpat_x_assum `_ /\ _ ==> !D explicit. gas_origin_ptr_path _ _ _ _` irule >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  drule_all default_bytes_decode_exact_sequence >> strip_tac >>
  `t = v with vs_inst_idx := initial.vs_inst_idx` by metis_tac[exec_result_11] >>
  pop_assum SUBST_ALL_TAC >>
  drule_all calldata_bytes_sequence_frame >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `ARB` assume_tac) >>
  `!name. not_fresh_at st name ==>
    FLOOKUP G' name = FLOOKUP G name /\
    FLOOKUP tn'.t_var name = FLOOKUP tn.t_var name` by
    (metis_tac[calldata_bytes_sequence_ghost_frame]) >>
  suspend "accepted_resources"
QED

Resume calldata_exact_bytes_joint_limit[accepted_resources]:
  qexistsl [`v`,`[]`,`G'`,`tn'`] >>
  asm_rewrite_tac[] >>
  conj_tac >-
    (rpt strip_tac >> irule clean_window_value_robust >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`tn'.t_mem`,`v.vs_memory`,`type_memory_size tv`] >>
     asm_rewrite_tac[] >>
     qpat_assum `!i. w2n _ <= i /\ _ ==> i NOTIN tn'.t_mem` mp_tac >>
     qpat_assum `w2n (n2w d:bytes32) = d` mp_tac >>
     qpat_assum `type_memory_size tv = 32 + _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ (OK v,G',tn')`
       (qspecl_then [`ARB`,`{}`] mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_exec) >>
     simp_tac (srw_ss()) [fragExecTheory.exit_result_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[calldata_alloca_inv_fields] >>
  conj_tac >- metis_tac[calldata_alloca_frontier_inv_fields] >>
  conj_tac >- rewrite_tac[LESS_EQ_REFL] >>
  conj_tac >-
    (qpat_assum `!op. abi_decoder_operand_live _ op ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac (srw_ss()) [eval_operand_def, lookup_var_def] >>
     rpt strip_tac >> first_x_assum drule >>
     Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
  conj_tac >-
    (qpat_assum `abi_decode_frame _ _ _ _` mp_tac >>
     qpat_assum `type_memory_size tv = 32 + _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decode_frame_def, abi_decode_footprint_frame_def,
       abi_footprint_disjoint_def] >> metis_tac[]) >>
  qpat_assum `fresh_vars_wrt limit (_ with vs_inst_idx := _)` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[fresh_vars_wrt_def]
QED

Finalise calldata_exact_bytes_joint_limit
