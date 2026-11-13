(* The compiled calldata decoder decodes exactly what the source-side
   decoder (vyperCalldata's cd_decode) does: it reverts when cd_decode
   rejects the calldata, and otherwise leaves cd_decode's value in memory.
   calldata_coherent_owned_run with the source value pinned down. *)
Theory calldataExact
Ancestors
  vyperCalldata calldataRecursiveExecution calldataBulkLive
  abiDecoderContract abiDecoderBulk calldataBulkLeaf abiDecoderFrameCompose
  calldataDynOwned arithmetic list calldataRegistration abiValueEncoding
  calldataFiniteTransport calldataWordLive calldataSourceWord
  calldataBytesLive abiEncoderInputFrame abiDecoderBytesTyped abiDecoderString
  calldataSourceCorrespondence calldataReconstruction abiCallerAllocation
  calldataExactStatic calldataExactBulkPack calldataSourceDecisions
  vyperValue valueEncodingProps
  abiDecoderCoherence abiDecoderFrame exprLowering vyperTyping valueEncodingDefs compileEnv
  calldataExactMembers calldataExactDyn calldataRecursiveProducers
  abiDecoderAppend abiDecoderMemberInfos
  calldataExactArrayAssembly calldataExactTupleAssembly calldataExactStructAssembly
  calldataExactLinkedMembers

Theorem calldata_bulk_live_frag_mem_mod_guard:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d+(32+maxn*mem_sz) < dimword (:256) /\
  d+(32+maxn*mem_sz) <= initial.vs_alloca_next ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn MOD dimword (:256) /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz) t.vs_memory =
        mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz)
          initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (32+maxn*mem_sz) initial t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p initial) /\
      ?t. r = Abort Revert_abort t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all calldata_bulk_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_live_prefix_safe_mod) >>
      qexistsl_tac [`src`,`p`,`mem_sz`,`maxn`,`ei`,`dst`,`d`,`abi_sz`] >> simp[]) >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn MOD dimword (:256)`
  >- (drule_all calldata_count_guard_accepted_bounds >> strip_tac >>
      `w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz <= maxn*mem_sz` by
        simp[LE_MULT_RCANCEL] >>
      `d+32 < dimword (:256) /\
       w2n (abi_decode_load CALLDATALOAD p initial)*mem_sz < dimword (:256)` by decide_tac >>
      drule_all calldata_bulk_accepted_live_mod >> strip_tac >>
      `abi_decode_frame d (32+maxn*mem_sz) initial t` by
        (irule abi_decode_frame_widen >> goal_assum (drule_at Any) >> simp[]) >>
      disj1_tac >> qexists_tac `t` >>
      gvs[instIdxIndepTheory.eval_op_inst_idx, abi_decode_frame_def] >> metis_tac[]) >>
  `maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_bulk_rejected_live_mod >> strip_tac >>
  disj2_tac >> qexists_tac `t` >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem calldata_exact_word_owned_run:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
   ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
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
      FLOOKUP v.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?c. type_to_abi_dec_info sf ce ty = DecPrimWord c` by
    metis_tac[word_type_decoder_primitive] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `type_memory_size tv = 32` by (irule abi_word_type_size >> metis_tac[]) >>
  `!cd pos. cd_decode F cd tv pos = cd_word_value tv (cd_word cd pos)` by
    (qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
     qpat_x_assum `is_word_type ty` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `ty` >> simp[is_word_type_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[is_word_type_def, cd_decode_def]) >>
  `d+32 <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> conj_tac
     >- (qpat_x_assum `d + type_memory_size tv <= _` mp_tac >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `d < dimword (:256)` by
    (qpat_x_assum `d + type_memory_size tv < _` mp_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all calldata_word_live_frag_mem_guard >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all calldata_finite_fragment_run_guard >> strip_tac
  >- (disj1_tac >> conj_tac
      >- (drule_all calldata_coherent_word_rejects >>
          simp[GSYM calldata_decode_load_word]) >>
      qexistsl_tac [`fuel`,`z`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `(\t. _) t` (strip_assume_tac o BETA_RULE) >>
  `cd_word_value tv (abi_decode_load CALLDATALOAD p initial) <> NONE` by
    (drule_all calldata_coherent_word_accepts >> simp[]) >>
  Cases_on `cd_word_value tv (abi_decode_load CALLDATALOAD p initial)`
  >- metis_tac[] >>
  rename1 `cd_word_value tv _ = SOME x` >>
  `value_has_type tv x /\ typed_val_to_w256 tv x = abi_decode_load CALLDATALOAD p initial` by
    (drule_all calldata_coherent_word_value >> metis_tac[]) >>
  `val_wf tv x` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >> asm_rewrite_tac[]) >>
  `val_in_memory tv x d t.vs_memory` by
    (irule calldata_word_representation >> asm_rewrite_tac[] >>
     qexistsl_tac [`env`,`ty`] >> asm_rewrite_tac[]) >>
  disj2_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` kall_tac >>
  qexistsl_tac [`t`,`x`,`[]`] >>
  asm_rewrite_tac[GSYM calldata_decode_load_word] >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> asm_rewrite_tac[] >>
    qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abiDecoderContractTheory.abi_decode_frame_def,
    abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED

Theorem calldata_exact_bytestring_reconstruction:
  (tv = BaseTV (BytesT (Dynamic maxn)) \/ tv = BaseTV (StringT maxn)) /\
  w2n (cd_word cd pos) <= maxn /\
  mem_word_at d mem = cd_word cd pos /\
  mem_bytes_at d (abi_decode_bytes_copy_size maxn) mem =
    mem_bytes_at pos (abi_decode_bytes_copy_size maxn) cd ==>
  ?x. cd_decode F cd tv pos = SOME x /\ value_has_type tv x /\
      val_wf tv x /\ val_in_memory tv x d mem
Proof
  strip_tac >>
  `32 + w2n (cd_word cd pos) <= abi_decode_bytes_copy_size maxn` by
    (mp_tac (cj 3 abi_decoder_bytes_copy_size |> Q.INST [`n` |-> `maxn`]) >> decide_tac) >>
  `mem_bytes_at (d+32) (w2n (cd_word cd pos)) mem =
   mem_bytes_at (pos+32) (w2n (cd_word cd pos)) cd` by
    (irule abi_encoder_window_slice >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> simp[cd_decode_def] >>
  gvs[cd_bytes_def, mem_bytes_at_def, value_has_type_def, val_in_memory_def,
    abi_decoder_string_memory, wordsTheory.n2w_w2n] >>
  irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
  simp[value_has_type_def]
QED

Theorem calldata_exact_bytestring_owned_run:
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
   ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
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
      FLOOKUP v.vs_allocas id = SOME (q,k))
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
     TRY (rename1 `BytesT b` >> Cases_on `b` >> simp[is_bytestring_type_def]) >>
     rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
     simp[type_to_abi_dec_info_def, type_memory_bytes_def, valueEncodingTheory.type_memory_size_def,
       vfmConstantsTheory.word_size_def, abiDecoderBytesTheory.abi_decode_bytes_copy_size_def]) >>
  `d+abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> conj_tac
     >- (qpat_x_assum `d + type_memory_size tv <= _` mp_tac >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `d+abi_decode_bytes_copy_size maxn < dimword (:256)` by
    (qpat_x_assum `d + type_memory_size tv < _` mp_tac >> asm_rewrite_tac[]) >>
  `maxn < dimword (:256)` by (drule abi_decode_bytes_extent_capacity_bound >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all calldata_bytes_live_frag_mem_guard >> disch_then (qspec_then `ctx` assume_tac) >>
  drule fragExecMemTheory.frag_exec_mem_pre_exit >>
  disch_then (qspecl_then [`\s. s = initial`,
    `\r. maxn < w2n (abi_decode_load CALLDATALOAD p initial) /\ ?z. r = Abort Revert_abort z`] mp_tac) >>
  simp_tac bool_ss [] >> impl_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  disch_tac >> drule_all calldata_finite_fragment_run_guard >> strip_tac
  >- (disj1_tac >> conj_tac
      >- (qpat_x_assum `MEM tv _` mp_tac >>
          simp_tac list_ss [MEM] >> strip_tac >>
          simp[cd_decode_def, GSYM calldata_decode_load_word]) >>
      qexistsl_tac [`fuel`,`z`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `(\t. _) t` (strip_assume_tac o BETA_RULE) >>
  `?x. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory` by
    (qpat_x_assum `MEM tv _` mp_tac >> simp_tac list_ss [MEM] >>
     disch_tac >> metis_tac[GSYM calldata_decode_load_word,
       calldata_exact_bytestring_reconstruction]) >>
  disj2_tac >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` kall_tac >>
  qexistsl_tac [`t`,`x`,`[]`] >> asm_rewrite_tac[] >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> asm_rewrite_tac[] >>
    qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abiDecoderContractTheory.abi_decode_frame_def,
    abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED

Theorem calldata_exact_bulk_array_owned_run:
  abi_decoder_coherent ce env sf ty tv /\ ty = ArrayT ety (Dynamic maxn) /\
  type_to_abi_dec_info sf ce ty = DecDynArray ei abi_sz mem_sz F maxn /\
  ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
   ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
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
      FLOOKUP v.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ty = _` SUBST_ALL_TAC >>
  `?etv. tv = ArrayTV etv (Dynamic maxn) /\
    abi_decoder_coherent ce env sf ety etv /\
    ei = type_to_abi_dec_info sf ce ety /\
    ~is_abi_dynamic ce.ce_struct_fields ety /\
    mem_sz = type_memory_size etv /\
    type_memory_size tv = 32+maxn*mem_sz` by
    (qpat_x_assum `type_to_abi_dec_info _ _ _ = _` mp_tac >>
     qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decoder_coherent_array_iff, type_to_abi_dec_info_def] >>
     rpt strip_tac >> qexists_tac `tv'` >> simp[] >>
     drule abi_decoder_coherent_header >>
     simp[abi_decoder_header_def, valueEncodingTheory.type_memory_size_def]) >>
  `maxn < dimword (:256)` by
    (qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), type_slot_size_def] >>
     rpt strip_tac >>
     rename1 `0 < type_slot_size elem` >>
     `maxn <= maxn * type_slot_size elem` by
       simp[LE_MULT_CANCEL_LBARE] >>
     decide_tac) >>
  `~tv_abi_dynamic etv /\ ~tv_needs_clamp etv /\
    tv_abi_size etv = type_memory_size etv` by
    (drule_all calldata_coherent_dynamic >>
     drule_all calldata_coherent_clamp >>
     simp[tv_abi_size_def] >> metis_tac[calldataSourceSizeTheory.tv_abi_static_memory_size]) >>
  `d+(32+maxn*mem_sz) <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> conj_tac
     >- (qpat_x_assum `d + type_memory_size tv <= _` mp_tac >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `d+(32+maxn*mem_sz) < dimword (:256)` by
    (qpat_x_assum `d + type_memory_size tv < _` mp_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _`
    (fn th => pure_rewrite_tac [th]) >> disch_tac >>
  drule_all calldata_bulk_live_frag_mem_mod_guard >> disch_then (qspec_then `ctx` assume_tac) >>
  drule fragExecMemTheory.frag_exec_mem_pre_exit >>
  disch_then (qspecl_then [`\s. s = initial`,
    `\r. maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p initial) /\ ?z. r = Abort Revert_abort z`] mp_tac) >>
  simp_tac bool_ss [] >> impl_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  disch_tac >> drule_all calldata_finite_fragment_run_guard >> strip_tac
  >- (disj1_tac >> conj_tac
      >- (qpat_x_assum `maxn MOD _ < _` mp_tac >>
          qpat_x_assum `maxn < dimword (:256)` mp_tac >>
          qpat_x_assum `tv = _` mp_tac >> rpt (pop_assum kall_tac) >>
          rpt strip_tac >> gvs[] >>
          simp[cd_decode_def, GSYM calldata_decode_load_word]) >>
      qexistsl_tac [`fuel`,`z`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `(\t. _) t` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac) >>
  `?x. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory` by
    (asm_rewrite_tac[] >> irule calldata_exact_bulk_pack >>
     conj_tac
     >- (rpt strip_tac >> irule calldata_exact_static_slice >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     asm_rewrite_tac[] >> qexists_tac `w2n (abi_decode_load CALLDATALOAD p initial)` >>
     qpat_x_assum `mem_bytes_at _ _ _ = _` mp_tac >>
     qpat_x_assum `mem_sz = _` mp_tac >>
     qpat_x_assum `w2n _ <= _` mp_tac >>
     qpat_x_assum `maxn < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
     simp[GSYM calldata_decode_load_word, wordsTheory.n2w_w2n,
       cd_at_def, wordsTheory.word_add_def]) >>
  disj2_tac >> qexistsl_tac [`t`,`x`,`[]`] >> asm_rewrite_tac[] >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> asm_rewrite_tac[] >>
    qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abiDecoderContractTheory.abi_decode_frame_def,
    abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> metis_tac[]
QED

Theorem calldata_exact_owned_run:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !dst src st final fn initial p d ctx site oid base_addr cap.
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),final) /\
  fn_has_code st final fn /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
  d+type_memory_size tv < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
   ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
    ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size tv)::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k))
Proof
  ho_match_mp_tac calldata_coherent_induction >>
  conj_tac >- suspend "base" >>
  conj_tac >- suspend "flag" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "tuple" >>
  suspend "struct"
QED

Resume calldata_exact_owned_run[base]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt)` by
    (irule (cj 1 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  Cases_on `is_word_type (BaseT bt)`
  >- (drule_all calldata_exact_word_owned_run >> disch_then ACCEPT_TAC) >>
  `is_bytestring_type (BaseT bt)` by
    (qpat_x_assum `~is_word_type _` mp_tac >>
     qpat_x_assum `abi_decoder_scalar_valid _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `bt` >> simp[is_word_type_def, is_bytestring_type_def] >>
     Cases_on `b` >> simp[abi_decoder_scalar_valid_def, is_word_type_def, is_bytestring_type_def]) >>
  drule_all calldata_exact_bytestring_owned_run >> disch_then ACCEPT_TAC
QED

Resume calldata_exact_owned_run[flag]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n)` by
    (irule (cj 2 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  `is_word_type (FlagT nsid)` by simp[is_word_type_def] >>
  drule_all calldata_exact_word_owned_run >> disch_then ACCEPT_TAC
QED

Resume calldata_exact_owned_run[array]:
  rpt gen_tac >>
  mp_tac calldata_exact_array_case >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC calldata_exact_aggregate_owned_run_linked_tail)) >>
  (impl_tac >- (BETA_TAC >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    `ArrayT ty (Dynamic n) = ArrayT ty (Dynamic n)` by simp[] >>
    `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) =
      DecDynArray (type_to_abi_dec_info sf ce ty)
        (abi_embedded_static_size ce.ce_struct_fields ty)
        (type_memory_bytes ce ty) F n` by
      (qpat_x_assum `~is_abi_dynamic _ _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[type_to_abi_dec_info_def]) >>
    drule_all calldata_exact_bulk_array_owned_run >> disch_then ACCEPT_TAC)) >>
  disch_then (ACCEPT_TAC o BETA_RULE)
QED
Resume calldata_exact_owned_run[tuple]:
  rpt gen_tac >> mp_tac calldata_exact_tuple_case >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> disch_then (ACCEPT_TAC o BETA_RULE)
QED
Resume calldata_exact_owned_run[struct]:
  rpt gen_tac >> mp_tac calldata_exact_struct_case >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> disch_then (MATCH_ACCEPT_TAC o BETA_RULE)
QED
Finalise calldata_exact_owned_run
