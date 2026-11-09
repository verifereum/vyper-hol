(* Typed reentrant finite decoder callbacks. *)
Theory calldataFiniteTyped
Ancestors
  calldataFiniteTransport calldataWordLive calldataReconstruction abiCallerAllocation
  abiDecoderFrame abiDecoderCoherence exprLowering compileEnv contractABI
  calldataBytesLive abiDecoderBytes calldataBulkLive

Theorem calldata_coherent_word_layout[local]:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty ==>
  (?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp) /\
  type_memory_size tv = 32
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  Cases_on `ty` >> gvs[is_word_type_def, type_to_abi_dec_info_def,
    type_memory_bytes_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_word_type_def, type_to_abi_dec_info_def, type_memory_bytes_def,
    AllCaseEqs()] >>
  Cases_on `b` >> gvs[is_word_type_def, type_to_abi_dec_info_def, type_memory_bytes_def]
QED

Theorem calldata_coherent_word_owned_run:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
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
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
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
  drule_all calldata_coherent_word_layout >> strip_tac >>
  `d+32 <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> conj_tac
     >- (qpat_x_assum `d + type_memory_size tv <= _` mp_tac >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `d < dimword (:256)` by
    (qpat_x_assum `d + type_memory_size tv < _` mp_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all calldata_word_live_frag_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all calldata_finite_fragment_run >> strip_tac
  >- metis_tac[] >>
  disj2_tac >>
  `?x. value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory` by
    (irule calldata_coherent_observed_word_typed >>
     qexistsl_tac [`ce`,`sf`,`env`,`ty`,`abi_decode_load CALLDATALOAD p initial`] >>
     qpat_x_assum `(\t. _) t` mp_tac >> asm_rewrite_tac[] >>
     simp_tac (srw_ss()) []) >>
  qpat_x_assum `(\t. _) t` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` kall_tac >>
  qexistsl_tac [`t`,`x`,`[]`] >>
  asm_rewrite_tac[] >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> asm_rewrite_tac[] >>
    qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abiDecoderContractTheory.abi_decode_frame_def,
    abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC
QED

Theorem calldata_coherent_bytes_layout[local]:
  abi_decoder_coherent ce env sf ty tv /\ ty = BaseT (BytesT (Dynamic maxn)) ==>
  type_to_abi_dec_info sf ce ty = DecBytestring maxn /\
  type_memory_size tv = abi_decode_bytes_copy_size maxn /\
  tv = BaseTV (BytesT (Dynamic maxn))
Proof
  strip_tac >> gvs[] >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, vyperValueTheory.evaluate_type_def,
    type_to_abi_dec_info_def, type_memory_bytes_def,
    abi_decode_bytes_copy_size_def]
QED

Theorem calldata_coherent_string_layout[local]:
  abi_decoder_coherent ce env sf ty tv /\ ty = BaseT (StringT maxn) ==>
  type_to_abi_dec_info sf ce ty = DecBytestring maxn /\
  type_memory_size tv = abi_decode_bytes_copy_size maxn /\
  tv = BaseTV (StringT maxn)
Proof
  strip_tac >> gvs[] >> drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, vyperValueTheory.evaluate_type_def,
    type_to_abi_dec_info_def, type_memory_bytes_def,
    abi_decode_bytes_copy_size_def]
QED

Theorem calldata_coherent_bytes_owned_run:
  abi_decoder_coherent ce env sf ty tv /\ ty = BaseT (BytesT (Dynamic maxn)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
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
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
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
  drule_all calldata_coherent_bytes_layout >> strip_tac >>
  `d+abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> conj_tac
     >- (qpat_x_assum `d + type_memory_size tv <= _` mp_tac >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `d+abi_decode_bytes_copy_size maxn < dimword (:256)` by
    (qpat_x_assum `d + type_memory_size tv < _` mp_tac >> asm_rewrite_tac[]) >>
  `maxn < dimword (:256)` by (drule abi_decode_bytes_extent_capacity_bound >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all calldata_bytes_live_frag_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule fragExecMemTheory.frag_exec_mem_pre_exit >>
  disch_then (qspecl_then [`\s. s = initial`,`\r. ?z. r = Abort Revert_abort z`] mp_tac) >>
  simp_tac bool_ss [] >> impl_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  disch_tac >> drule_all calldata_finite_fragment_run >> strip_tac
  >- metis_tac[] >>
  qpat_x_assum `(\t. _) t` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac) >>
  `?x. value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory` by
    (asm_rewrite_tac[] >> irule calldata_observed_bytes_typed >>
     qexists_tac `w2n (abi_decode_load CALLDATALOAD p initial)` >>
     asm_rewrite_tac[wordsTheory.n2w_w2n]) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  disj2_tac >> qexistsl_tac [`t`,`x`,`[]`] >> asm_rewrite_tac[] >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> asm_rewrite_tac[] >>
    qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abiDecoderContractTheory.abi_decode_frame_def,
    abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!fuel r. _` (qspecl_then [`fuel`,`run_from fuel ctx fn t`] mp_tac) >>
      asm_rewrite_tac[]) >> first_assum ACCEPT_TAC
QED

Theorem calldata_coherent_string_owned_run:
  abi_decoder_coherent ce env sf ty tv /\ ty = BaseT (StringT maxn) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
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
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
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
  drule_all calldata_coherent_string_layout >> strip_tac >>
  `d+abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> conj_tac
     >- (qpat_x_assum `d + type_memory_size tv <= _` mp_tac >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `d+abi_decode_bytes_copy_size maxn < dimword (:256)` by
    (qpat_x_assum `d + type_memory_size tv < _` mp_tac >> asm_rewrite_tac[]) >>
  `maxn < dimword (:256)` by (drule abi_decode_bytes_extent_capacity_bound >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_all calldata_bytes_live_frag_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule fragExecMemTheory.frag_exec_mem_pre_exit >>
  disch_then (qspecl_then [`\s. s = initial`,`\r. ?z. r = Abort Revert_abort z`] mp_tac) >>
  simp_tac bool_ss [] >> impl_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  disch_tac >> drule_all calldata_finite_fragment_run >> strip_tac
  >- metis_tac[] >>
  qpat_x_assum `(\t. _) t` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac) >>
  `?x. value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory` by
    (asm_rewrite_tac[] >> irule calldata_observed_string_typed >>
     qexists_tac `w2n (abi_decode_load CALLDATALOAD p initial)` >>
     asm_rewrite_tac[wordsTheory.n2w_w2n]) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  disj2_tac >> qexistsl_tac [`t`,`x`,`[]`] >> asm_rewrite_tac[] >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> asm_rewrite_tac[] >>
    qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abiDecoderContractTheory.abi_decode_frame_def,
    abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!fuel r. _` (qspecl_then [`fuel`,`run_from fuel ctx fn t`] mp_tac) >>
      asm_rewrite_tac[]) >> first_assum ACCEPT_TAC
QED

Theorem calldata_unclamped_dynamic_pack[local]:
  abi_decoder_coherent ce env sf ty tv /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\
  n <= maxn /\ mem_word_at d mem = n2w n ==>
  ?x. value_has_type (ArrayTV tv (Dynamic maxn)) x /\
    val_wf (ArrayTV tv (Dynamic maxn)) x /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) x d mem
Proof
  strip_tac >>
  `!i. i < n ==> ?v. value_has_type tv v /\
    val_in_memory tv v (d+32+i*type_memory_size tv) mem` by
    (rpt strip_tac >> drule_all calldata_unclamped_static_typed >>
     disch_then (qspecl_then [`d+32+i*type_memory_size tv`,`mem`] mp_tac) >>
     metis_tac[]) >>
  drule calldata_fixed_witnesses >> strip_tac >>
  qexists_tac `ArrayV (make_array_value tv (Dynamic maxn) vs)` >>
  irule calldata_dynamic_values_typed_memory >> simp[]
QED

Theorem calldata_coherent_bulk_layout[local]:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn ==>
  ?etv. tv = ArrayTV etv (Dynamic maxn) /\
    abi_decoder_coherent ce env sf ety etv /\
    ei = type_to_abi_dec_info sf ce ety /\
    ~is_abi_dynamic ce.ce_struct_fields ety /\
    mem_sz = type_memory_size etv /\
    type_memory_size tv = 32+maxn*mem_sz
Proof
  simp[abi_decoder_coherent_array_iff, type_to_abi_dec_info_def] >>
  rpt strip_tac >> qexists_tac `tv'` >> simp[] >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def, valueEncodingTheory.type_memory_size_def]
QED

Theorem calldata_coherent_bulk_array_owned_run:
  abi_decoder_coherent ce env sf ty tv /\ ty = ArrayT ety (Dynamic maxn) /\
  type_to_abi_dec_info sf ce ty = DecDynArray ei abi_sz mem_sz F maxn /\
  ~dec_info_needs_clamp ei /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
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
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
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
  drule_all calldata_coherent_bulk_layout >> strip_tac >>
  `d+(32+maxn*mem_sz) <= initial.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cap`,`oid`,`base_addr`] >> conj_tac
     >- (qpat_x_assum `d + type_memory_size tv <= _` mp_tac >> asm_rewrite_tac[]) >>
     first_assum ACCEPT_TAC) >>
  `d+(32+maxn*mem_sz) < dimword (:256)` by
    (qpat_x_assum `d + type_memory_size tv < _` mp_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_to_abi_dec_info _ _ _ = _` (fn th => pure_rewrite_tac [th]) >> disch_tac >>
  drule_all calldata_bulk_live_frag_mem_mod >> disch_then (qspec_then `ctx` assume_tac) >>
  drule fragExecMemTheory.frag_exec_mem_pre_exit >>
  disch_then (qspecl_then [`\s. s = initial`,`\r. ?z. r = Abort Revert_abort z`] mp_tac) >>
  simp_tac bool_ss [] >> impl_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  disch_tac >> drule_all calldata_finite_fragment_run >> strip_tac
  >- metis_tac[] >>
  qpat_x_assum `(\t. _) t` (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac) >>
  `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn` by
    (`maxn MOD dimword (:256) <= maxn` by simp[arithmeticTheory.MOD_LESS_EQ] >> decide_tac) >>
  `?x. value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory` by
    (asm_rewrite_tac[] >> irule calldata_unclamped_dynamic_pack >>
     conj_tac
     >- (qexists_tac `w2n (abi_decode_load CALLDATALOAD p initial)` >>
         asm_rewrite_tac[wordsTheory.n2w_w2n]) >>
     qexistsl_tac [`ce`,`env`,`sf`,`ety`] >> asm_rewrite_tac[] >>
     qpat_x_assum `~dec_info_needs_clamp ei` mp_tac >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`t`,`x`,`[]`] >> asm_rewrite_tac[] >>
  `alloca_inv t` by (irule calldata_alloca_inv_fields >> asm_rewrite_tac[] >>
    qexists_tac `initial` >> asm_rewrite_tac[]) >>
  `alloca_frontier_inv ctx fn site t` by
    (irule calldata_alloca_frontier_inv_fields >> qexists_tac `initial` >> asm_rewrite_tac[]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp_tac std_ss [abiDecoderContractTheory.abi_decode_frame_def,
    abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!fuel r. _` (qspecl_then [`fuel`,`run_from fuel ctx fn t`] mp_tac) >>
      asm_rewrite_tac[]) >>
  qpat_x_assum `!p k. _` mp_tac >> asm_rewrite_tac[]
QED
