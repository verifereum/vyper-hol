(* The allocation-free leaves of the owned source decoder contract: primitive
   words and bytestrings, and dynamic arrays of static elements without clamp
   (copied in bulk).  Neither allocates scratch. *)
Theory sourceOwnedLeafPtr
Ancestors
  sourceOwnedArrayLoopPtr sourcePrimitiveReentryPtr abiDecoderSequenceReach
  decoderPrimitiveObservations decoderWorldFramePtr
  abiDecoderClampedWord abiDecoderBytesTyped abiValueEncoding
  abiDecoderCoherence sourceBytesRepresentation calldataDecodePtr abiDecoderReentry
  venomState abiDecoderBytes calldataDynOwned abiDecoderFrameCompose
  allocaFrontierBound allocaBudgetProps venomMemDefs ptrDiscipline bodyPtrDefs arithmetic

Theorem source_owned_primitive_decoder_ptr:
  abi_decoder_coherent ce env sf ty tv /\
  ((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\ is_word_type ty) \/
   (?m. type_to_abi_dec_info sf ce ty = DecBytestring m)) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `evaluate_type env ty = SOME tv /\
   type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
       is_word_type ty /\ type_memory_size tv = 32) \/
    (?m. type_to_abi_dec_info sf ce ty = DecBytestring m /\
       type_memory_size tv = abi_decode_bytes_copy_size m /\ m < dimword (:256)))` by
    (qpat_x_assum `(?clamp. _ /\ is_word_type ty) \/ _` strip_assume_tac
     >- metis_tac[abi_word_type_size] >>
     drule_all coherent_source_bytes_representation >> strip_tac >>
     disj2_tac >> qexists `m` >>
     `m < dimword (:256)` by
       (mp_tac (Q.INST [`n` |-> `m`] abi_decoder_bytes_copy_size) >> decide_tac) >>
     metis_tac[]) >> (
  `type_memory_size tv < dimword (:256) /\ e < dimword (:256) /\
    srcpos < dimword (:256)` by decide_tac >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  `?t H u.
    run_inst_seq (emitted_insts middle end_st) r = OK (t with vs_inst_idx := r.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ptr_covers H u child t (type_memory_size tv) /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem) /\
    abi_decode_frame e (type_memory_size tv) r t /\ fresh_vars_wrt limit t /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
    (!op w. (!x. op = Var x ==> not_fresh_at middle x) /\ eval_operand op r = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r)` by
    (irule source_primitive_decoder_reentry_ptr >>
     metis_tac[]) >>
  drule decoder_primitive_code_shape >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `abi_decode_sim ctx fn r t` by
    (drule_all abi_decoder_run_sequence_reach >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >>
     drule decoder_primitive_old_operand >>
     disch_then (qspecl_then [`t with vs_inst_idx := r.vs_inst_idx`,`r`,`op`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     simp[eval_operand_def, lookup_var_def]) >>
  drule_all decoder_run_world_frame >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qexistsl [`t`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_frame_footprint] >>
  conj_tac >-
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     pure_asm_rewrite_tac [allocas_from_def] >> simp_tac bool_ss []) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  `lookup_var root t = lookup_var root r` by
    (qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` (qspec_then `Var root` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `ptr_covers G tn root r outsz` mp_tac >>
  pure_rewrite_tac[ptr_covers_def] >>
  `FLOOKUP H root = FLOOKUP G root /\ op_taint u (Var root) = op_taint tn (Var root)` by
    metis_tac[] >>
  pure_asm_rewrite_tac[] >> simp_tac bool_ss [])
QED

Theorem source_owned_bulk_array_ptr:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  ~is_abi_dynamic ce.ce_struct_fields ety /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ety) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn))) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env (ArrayT ety (Dynamic maxn)) v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next
Proof
  cheat
QED
