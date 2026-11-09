(* Initializer inputs for an array nested inside an enclosing allocation. *)
Theory entryReachBodyNestedOwnedPath
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyOwnedBytesArray entryReachBodyCanonicalChildAddress
  entryReachBodyReentryResources entryReachBodyOwnedLoop
  entryReachBodyOwnedRegion entryReachBodyCanonicalBytesArray
  abiDecoderArrayLoopInit abiDecoderDynamicLoopSetup
  abiAllocationHistory allocaFrontierBound allocaBudgetProps
  venomMemDefs venomState compileEnv finite_map words list arithmetic
  context ctorAbiActualArrayRun

(* Checked one-slot arena regression: reuse executes at the arena end,
   where the former unconditional fresh-slot margin is false. *)
Theorem nested_counter_arena_end_probe[local]:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,32) /\
  s.vs_alloca_next = b+32 ==>
  (FLOOKUP s.vs_allocas inst.inst_id = NONE ==> s.vs_alloca_next+32 <= b+32) /\
  ~ (s.vs_alloca_next+32 <= b+32) /\
  ?t. step_inst_base inst s = OK t /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = b+32
Proof
  strip_tac >> simp[] >>
  drule_all actualAllocExecTheory.actual_word_alloca_reuse_run >>
  metis_tac[]
QED

Theorem nested_initializer_resources[local]:
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  entry_owned_loop_resources ctx fn site cid p oid root extent d sz s /\
  d <= cell /\ cell+csz <= d+sz /\ 32 <= csz /\
  b <= s.vs_alloca_next /\ (FLOOKUP s.vs_allocas header_st.cs_next_id = NONE ==> s.vs_alloca_next+32 <= b+cap) /\
  (!q. FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (q,32) ==>
    b <= q /\ q+32 <= b+cap) ==>
  ?q. entry_array_init_resources dst src maxn abi_sz
      (st,guard_st,header_st,loop_st,ip,cnt)
      (ctx,fn,site,cell,csz,b,cap,q,s)
Proof
  strip_tac >>
  qpat_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_owned_loop_resources_def]) >>
  drule_all entry_index_counter_readiness >> strip_tac >>
  qexists_tac `p'` >>
  simp_tac bool_ss [entry_array_init_resources_def] >>
  `abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
     ((ip,cnt),loop_st)` by
    simp[abi_decode_array_loop_init_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
  `cell+csz <= s.vs_alloca_next` by
    (fs[entry_owned_region_def, alloca_inv_def, alloca_next_valid_def] >>
     `root+extent <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  drule ctor_actual_function_ids >> strip_tac >> fs[] >> metis_tac[]
QED

Theorem nested_address_resources[local]:
  entry_owned_loop_resources ctx fn site cid p oid root extent d sz s /\
  abi_decoder_address_frame next s t /\
  d <= cell /\ cell+csz <= d+sz ==>
  entry_owned_loop_resources ctx fn site cid p oid root extent d sz t /\
  entry_owned_region oid root extent cell csz t
Proof
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    fs[abi_decoder_address_frame_def] >>
  `remaining_alloca_budget (fn_insts fn) t = remaining_alloca_budget (fn_insts fn) s` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  fs[entry_owned_loop_resources_def, entry_owned_region_def,
     alloca_frontier_inv_def, abi_alloca_history_def, alloca_inv_def,
     allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem entry_nested_owned_initializer_boundary:
  ity = ArrayT ty (Dynamic inner) /\ itv = ArrayTV tv (Dynamic inner) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ity) (abi_embedded_static_size ce.ce_struct_fields ity)
    (type_memory_bytes ce ity) st = (ops,middle) /\
  abi_decoder_coherent ce env sf (ArrayT ity (Dynamic outer)) (ArrayTV itv (Dynamic outer)) /\
  abi_decoder_metadata ce env (ArrayT ity (Dynamic outer)) (ArrayTV itv (Dynamic outer))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ity) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ity)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ity (Dynamic outer))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ity)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env ity)) (ListV avs) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st middle fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
    (type_memory_bytes ce (ArrayT ity (Dynamic outer))) s /\
  abi_decode_dynarray_prefix (FST (SND ops)) CALLDATALOAD (Lit 0w) inner
    (abi_embedded_static_size ce.ce_struct_fields ty) middle = ((),guard_st) /\
  abi_decode_array_header (SND (SND ops)) (FST (SND ops)) CALLDATALOAD guard_st =
    (cnt,header_st) /\
  abi_decode_index_init header_st = (iip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  b <= s.vs_alloca_next /\ (FLOOKUP s.vs_allocas header_st.cs_next_id = NONE ==> s.vs_alloca_next+32 <= b+cap) /\
  (!q. FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (q,32) ==>
    b <= q /\ q+32 <= b+cap) ==>
  ?u q. eval_operand (FST ops) u = SOME (n2w j) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_address_frame st.cs_next_var s u /\
    entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\ fresh_vars_wrt limit_st u /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ity (Dynamic outer))) u /\
    entry_owned_region oid root extent (d+32+j*type_memory_bytes ce ity)
      (type_memory_bytes ce ity) u /\
    abi_alloca_history (fn_insts fn) u /\
    abi_decoder_coherent ce env sf ity itv /\
    abi_decoder_metadata ce env ity itv (type_to_abi_dec_info ce.ce_struct_fields ce ity)
      (EL j avs) (EL j xs) /\
    abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
    mem_bytes_at (sb+abi_array_child_offset NONE (vyper_to_abi_type env ity) avs j)
      (LENGTH (enc (vyper_to_abi_type env ity) (EL j avs)))
      (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ity) (EL j avs) /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) (FST (SND ops)) (SND (SND ops)) 0
      (sb+abi_array_child_offset NONE (vyper_to_abi_type env ity) avs j)
      (LENGTH (enc (vyper_to_abi_type env ity) (EL j avs)))
      (d+32+j*type_memory_bytes ce ity) (type_memory_bytes ce ity) b cap u /\
    entry_array_init_resources (SND (SND ops)) (FST (SND ops)) inner
      (abi_embedded_static_size ce.ce_struct_fields ty)
      (middle,guard_st,header_st,loop_st,iip,cnt)
      (ctx,fn,site,d+32+j*type_memory_bytes ce ity,type_memory_bytes ce ity,b,cap,q,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_canonical_dynamic_child_address >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  `32 <= type_memory_bytes ce ity` by simp[Once type_memory_bytes_def] >>
  `abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) (FST (SND ops)) (SND (SND ops)) 0
     (sb+abi_array_child_offset NONE (vyper_to_abi_type env ity) avs j)
     (LENGTH (enc (vyper_to_abi_type env ity) (EL j avs)))
     (d+32+j*type_memory_bytes ce ity) (type_memory_bytes ce ity) b cap raw` by
    (qpat_x_assum `ity = _` kall_tac >>
     qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     simp_tac bool_ss [abiDecoderTypedContractTheory.abi_decoder_ranges_def] >>
     strip_tac >> simp[Excl "enc_def"] >> rpt conj_tac >> decide_tac) >>
  suspend "endpoint"
QED

Resume entry_nested_owned_initializer_boundary[endpoint]:
  qpat_x_assum `ity = _` kall_tac >>
  qpat_x_assum `itv = _` kall_tac >>
  `d <= d+32+j*type_memory_bytes ce ity` by decide_tac >>
  drule_all nested_address_resources >> strip_tac >>
  `raw.vs_allocas = s.vs_allocas /\ raw.vs_alloca_next = s.vs_alloca_next` by
    fs[abi_decoder_address_frame_def] >>
  `?q. entry_array_init_resources (SND (SND ops)) (FST (SND ops)) inner
     (abi_embedded_static_size ce.ce_struct_fields ty)
     (middle,guard_st,header_st,loop_st,iip,cnt)
     (ctx,fn,site,d+32+j*type_memory_bytes ce ity,type_memory_bytes ce ity,b,cap,q,raw)` by
    (irule nested_initializer_resources >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  suspend "pc"
QED

Resume entry_nested_owned_initializer_boundary[pc]:
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_shape >> strip_tac >>
  `entry_decode_path ctx fn s (raw with vs_inst_idx := LENGTH middle.cs_current_insts)` by
    (irule entryReachBodyOperationalPathTheory.entry_decode_emitted_path >>
     asm_rewrite_tac[] >> goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  `raw.vs_current_bb = s.vs_current_bb` by
    (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
     qexists_tac `emitted_insts st middle` >> asm_rewrite_tac[] >>
     rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[venomInstPropsTheory.step_preserves_control_flow,
               venomExecSemanticsTheory.step_inst_non_invoke]) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH middle.cs_current_insts`, `q`] >>
  simp[Excl "enc_def"] >> suspend "record_frame"
QED
Resume entry_nested_owned_initializer_boundary[record_frame]:
  rpt conj_tac
  >- (qpat_assum `abi_decoder_address_frame _ s raw` mp_tac >>
      simp_tac (srw_ss()) [abi_decoder_address_frame_def, eval_operand_def])
  >- (qpat_assum `entry_loop_fields s raw` mp_tac >>
      simp_tac (srw_ss()) [entryReachBodyExactArrayLoopTheory.entry_loop_fields_def])
  >- (qpat_assum `abi_decoder_address_frame _ s raw` mp_tac >>
      qpat_assum `~s.vs_halted` mp_tac >>
      simp_tac (srw_ss()) [abi_decoder_address_frame_def])
  >- (qpat_assum `fresh_vars_wrt _ raw` mp_tac >>
      simp_tac (srw_ss()) [fresh_vars_wrt_def])
  >- (qpat_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ raw` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp_tac (srw_ss()) [entry_owned_loop_resources_def, entry_owned_region_def,
        abi_alloca_history_def, alloca_frontier_inv_def, remaining_alloca_budget_def,
        alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (qpat_assum `entry_owned_region _ _ _ (_ + _) _ raw` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp_tac (srw_ss()) [entry_owned_region_def, ADD_ASSOC] >>
      metis_tac[ADD_ASSOC, ADD_COMM])
  >- (qpat_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ raw` mp_tac >>
      simp_tac (srw_ss()) [entry_owned_loop_resources_def, abi_alloca_history_def])
  >- (qpat_assum `mem_bytes_at _ _ (abi_decode_source _ raw) = _` mp_tac >>
      simp_tac (srw_ss()) [abiDecoderContractTheory.abi_decode_source_def])
  >- (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ raw` mp_tac >>
      simp_tac (srw_ss()) [abiDecoderTypedContractTheory.abi_decoder_ranges_def,
        eval_operand_def, AC ADD_ASSOC ADD_COMM, Excl "enc_def"])
  >> qpat_assum `entry_array_init_resources _ _ _ _ _ (_,_,_,_,_,_,_,_,raw)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [entry_array_init_resources_def, alloca_frontier_inv_def,
    remaining_alloca_budget_def, alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def, AC ADD_ASSOC ADD_COMM, Excl "enc_def"] >> metis_tac[]
QED
Finalise entry_nested_owned_initializer_boundary
