Theory dispatchedDecoderScalarJoint
Ancestors
  calldataExact dispatchedDecoderWordJoint calldataWordLive calldataSourceWord
  calldataReconstruction abiCallerAllocation abiDecoderCoherence abiDecoderClamp
  entryDecodeProps calldataWordProps vyperCalldata vyperValue valueEncodingTyping
  abiDecoderContract abiDecoderClampedWord abiDecoderFrameCompose
  compileEnv exprLowering words list arithmetic abiDecoderSigned integer_word
  calldataRegistration abiValueEncoding calldataSourceCorrespondence
  calldataFiniteTransport calldataWordLeaf fragGasOriginPtrExec abiDecoderFrame fragExec
  calldataDecodePtr calldataBytesLive calldataBytesLeaf calldataDynOwned abiDecoderBytes

Theorem calldata_exact_word_clamp_valid[local]:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  cd_decode F cd tv pos = SOME x ==>
  cd_word_value tv (cd_word cd pos) = SOME x /\
  abi_decoder_clamp_valid clamp (cd_word cd pos)
Proof
  strip_tac >>
  `cd_word_value tv (cd_word cd pos) = SOME x` by
    (qpat_assum `cd_decode F cd tv pos = SOME x` mp_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
     qpat_x_assum `is_word_type ty` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `ty` >> simp[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[is_word_type_def, cd_decode_def]) >>
  `abi_clamp_ok clamp (cd_word cd pos)` by
    (drule_all calldata_coherent_word_accepts >> metis_tac[optionTheory.NOT_SOME_NONE]) >>
  Cases_on `ty` >> gvs[is_word_type_def] >>
  gvs[abi_decoder_coherent_base_iff, abi_decoder_coherent_flag_iff] >>
  rpt strip_tac >> gvs[] >>
  gvs[type_to_abi_dec_info_def, cd_decode_def, cd_word_value_def,
    abi_decoder_clamp_valid_def, AllCaseEqs()] >>
  Cases_on `b` >> gvs[is_word_type_def, type_to_abi_dec_info_def,
    abi_decoder_scalar_valid_def, cd_decode_def, cd_word_value_def,
    abi_decoder_clamp_valid_def, type_to_abi_clamp_def, AllCaseEqs()] >>
  gvs[abi_decoder_header_def, evaluate_type_def, AllCaseEqs()] >>
  gvs[is_word_type_def, type_to_abi_dec_info_def, type_to_abi_clamp_def,
    cd_decode_def, cd_word_value_def, abi_decoder_clamp_valid_def,
    abi_clamp_ok_def, AllCaseEqs()]
QED

Theorem calldata_exact_word_accepted_joint:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  eval_operand src initial = SOME p /\ eval_operand (Var root) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
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
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fresh_vars_wrt st initial /\ ptr_covers G tn root initial (type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\ allocas_from lo initial /\
  ~ctx_has_dalloca ctx /\ cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x ==>
  ?v H u.
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    v.vs_allocas = initial.vs_allocas /\ v.vs_alloca_next = initial.vs_alloca_next /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame [(d,type_memory_size tv)] initial v /\
    fresh_vars_wrt last v /\ ptr_covers H u root v (type_memory_size tv) /\
    (!a. d <= a /\ a < d+type_memory_size tv ==> a NOTIN u.t_mem) /\
    u.t_mem SUBSET tn.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!z. not_fresh_at st z ==> FLOOKUP H z = FLOOKUP G z /\
      op_taint u (Var z) = op_taint tn (Var z)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u v) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn initial) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp` by
    metis_tac[word_type_decoder_primitive] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `type_memory_size tv = 32` by (irule abi_word_type_size >> metis_tac[]) >>
  drule_all calldata_exact_word_clamp_valid >> strip_tac >>
  `abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD p initial)` by
    simp[calldata_decode_load_word] >>
  `d+32 <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> simp[]) >>
  `d < dimword (:256)` by decide_tac >>
  `w2n (n2w d:bytes32) = d` by simp[] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `ptr_covers G tn root initial 32 /\
   w2n (n2w d:bytes32)+32 <= initial.vs_alloca_next` by metis_tac[] >>
  drule_all calldata_word_accepted_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial)` by
    (simp[calldata_decode_load_word] >> drule_all calldata_coherent_word_accepts >>
     metis_tac[optionTheory.NOT_SOME_NONE]) >>
  drule_all calldata_word_accepted_sequence >> strip_tac >>
  `t = s' with vs_inst_idx := initial.vs_inst_idx` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `abi_decode_frame d 32 initial s'` by
    (qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_frame_def] >> metis_tac[]) >>
  `fresh_vars_wrt last s'` by
    metis_tac[abiEncoderPathPropsTheory.fresh_vars_wrt_inst_idx] >>
  `value_has_type tv x /\ typed_val_to_w256 tv x = cd_word initial.vs_call_ctx.cc_calldata (w2n p)` by
    (drule_all calldata_coherent_word_value >> metis_tac[]) >>
  `val_wf tv x` by
    (irule (cj 1 value_has_type_val_wf) >> asm_rewrite_tac[]) >>
  `val_in_memory tv x d s'.vs_memory` by
    (irule calldata_word_representation >> conj_tac
     >- (qpat_x_assum `mem_word_at (w2n _) _ = _` mp_tac >>
         asm_rewrite_tac[calldata_decode_load_word]) >>
     conj_tac >- (qexistsl_tac [`env`,`ty`] >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `alloca_frontier_inv ctx fn site s'` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  drule_all calldata_word_accepted_live >> strip_tac >>
  `t = s' with vs_inst_idx := initial.vs_inst_idx` by
    metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op s' = eval_operand op initial` by
    (qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` mp_tac >>
     simp_tac (srw_ss()) [venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  `type_memory_bytes ce ty = 32` by metis_tac[] >>
  qpat_x_assum `abi_decode_frame d 32 initial s'` mp_tac >>
  simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
  qexistsl_tac [`s'`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _` 
        (qspecl_then [`ARB`,`ARB`] mp_tac) >>
      disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_exec) >>
      fs[exit_result_def] >> metis_tac[]) >>
  simp_tac bool_ss [abi_decode_footprint_frame_def, abi_footprint_disjoint_def,
    listTheory.MEM] >> metis_tac[]
QED

Theorem calldata_exact_bytestring_accepted_joint:
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  eval_operand src initial = SOME p /\ eval_operand (Var root) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
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
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fresh_vars_wrt st initial /\ ptr_covers G tn root initial (type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\ allocas_from lo initial /\
  ~ctx_has_dalloca ctx /\ cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x ==>
  ?v H u.
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    v.vs_allocas = initial.vs_allocas /\ v.vs_alloca_next = initial.vs_alloca_next /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame [(d,type_memory_size tv)] initial v /\
    fresh_vars_wrt last v /\ ptr_covers H u root v (type_memory_size tv) /\
    (!a. d <= a /\ a < d+type_memory_size tv ==> a NOTIN u.t_mem) /\
    u.t_mem SUBSET tn.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!z. not_fresh_at st z ==> FLOOKUP H z = FLOOKUP G z /\
      op_taint u (Var z) = op_taint tn (Var z)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u v) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn initial) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `?maxn. type_to_abi_dec_info sf ce ty = DecBytestring maxn /\
    type_memory_size tv = abi_decode_bytes_copy_size maxn /\
    MEM tv [BaseTV (BytesT (Dynamic maxn)); BaseTV (StringT maxn)]` by
    (qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
     qpat_x_assum `is_bytestring_type ty` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `ty` >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def, is_bytestring_type_def, AllCaseEqs()] >>
     simp[type_to_abi_dec_info_def, type_memory_bytes_def, valueEncodingTheory.type_memory_size_def,
       vfmConstantsTheory.word_size_def, abi_decode_bytes_copy_size_def]) >>
  `d+abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> metis_tac[]) >>
  `d+abi_decode_bytes_copy_size maxn < dimword (:256)` by metis_tac[] >>
  `maxn < dimword (:256)` by (drule abi_decode_bytes_extent_capacity_bound >> simp[]) >>
  `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn` by
    (qpat_x_assum `cd_decode F _ _ _ = SOME x` mp_tac >>
     qpat_x_assum `MEM tv _` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[MEM] >> strip_tac >> simp[Once cd_decode_def, GSYM calldata_decode_load_word, AllCaseEqs()] >>
     metis_tac[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all calldata_bytes_accepted_live >> strip_tac >>
  `not_fresh_at st root /\ (!q. src = Var q ==> not_fresh_at st q)` by
    metis_tac[calldata_operand_live_not_fresh] >>
  `d < dimword (:256) /\ abi_decode_bytes_copy_size maxn < dimword (:256)` by decide_tac >>
  `w2n (n2w d:bytes32) = d` by simp[] >>
  `abi_decode_load CALLDATALOAD p initial =
    n2w (w2n (abi_decode_load CALLDATALOAD p initial))` by simp[] >>
  `ptr_covers G tn root initial (abi_decode_bytes_copy_size maxn)` by metis_tac[] >>
  `abi_decode_bytes_copy_size maxn = 32 + 32 * ((maxn + 31) DIV 32)` by
    simp[NoAsms, abi_decode_bytes_copy_size_def] >>
  drule_all calldata_bytestring_overwrite_endpoint_core_uniform_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qpat_x_assum `abi_decode_load CALLDATALOAD p initial = n2w _` kall_tac >>
  `t = s' with vs_inst_idx := initial.vs_inst_idx` by
    metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  `alloca_inv s' /\
   !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (initial,G,tn) [] (OK s',G',tn')` by
    (qpat_x_assum `alloca_inv initial /\ _ ==> _` mp_tac >>
     impl_tac >- (asm_rewrite_tac[] >> (metis_tac [LESS_MOD])) >> simp_tac bool_ss []) >>
  `value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d s'.vs_memory` by
    (`w2n (cd_word initial.vs_call_ctx.cc_calldata (w2n p)) <= maxn` by
       metis_tac[calldata_decode_load_word] >>
     `mem_word_at d s'.vs_memory = cd_word initial.vs_call_ctx.cc_calldata (w2n p)` by
       metis_tac[calldata_decode_load_word] >>
     drule_all calldata_exact_bytestring_reconstruction >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `alloca_frontier_inv ctx fn site s'` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >>
     metis_tac[abi_decode_frame_def]) >>
  drule_all calldata_bytes_accepted_allocation >> strip_tac >>
  `t = s' with vs_inst_idx := initial.vs_inst_idx` by
    metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `fresh_vars_wrt last s'` by
    metis_tac[abiEncoderPathPropsTheory.fresh_vars_wrt_inst_idx] >>
  qexistsl_tac [`s'`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qpat_x_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
        (qspecl_then [`ARB`,`ARB`] mp_tac) >>
      rpt (pop_assum kall_tac) >>
      disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_exec) >>
      gvs[exit_result_def] >> metis_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  `type_memory_bytes ce ty = abi_decode_bytes_copy_size maxn` by metis_tac[] >>
  `d MOD dimword (:256) = d` by metis_tac[LESS_MOD] >>
  simp_tac bool_ss [abi_decode_footprint_frame_def, abi_footprint_disjoint_def,
    listTheory.MEM] >>
  asm_rewrite_tac[] >> metis_tac[]
QED
