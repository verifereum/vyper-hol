(* The bulk decoder needs source conversion, not aggregate ABI typing. *)
Theory entryReachBodySourceBulkEndpoint
Ancestors
  entryReachBodyBulkCore entryReachBodySourceMemberEntry
  abiDecoderBulk abiDecoderContract abiDecoderCoherence abiDecoderTypedContract
  compileEnv exprLowering vyperABI vyperTyping valueEncoding vyperValue contractABI
  words list arithmetic byte venomState abiStaticLayoutProps
  entryReachBodyOwnedRegion entryReachBodyScratchSet entryReachBodyExactArrayLoop
  entryReachBodyOperationalPath abiEncoderRegisteredEffect abiAllocationHistory
  allocaFrontierBound venomMemDefs

Theorem source_bulk_values[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) = DecDynArray ei abi_sz mem_sz F maxn /\
  ~dec_info_needs_clamp ei /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    root_di (ListV avs) (ArrayV (DynArrayV xs)) ==>
  static_layout_compatible ce env ty tv /\ all_have_type tv xs /\
  vyper_to_abi_same env ty xs = SOME avs /\ LENGTH xs <= maxn /\
  abi_sz = type_memory_size tv /\ mem_sz = type_memory_size tv /\
  maxn < dimword (:256) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * mem_sz
Proof
  strip_tac >>
  `DecDynArray ei abi_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  qpat_x_assum `entry_source_metadata _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [entry_source_metadata_def] >> strip_tac >>
  `vyper_to_abi_same env ty xs = SOME avs` by
    (qpat_x_assum `vyper_to_abi env (ArrayT _ _) _ = _` mp_tac >>
     simp[Once vyper_to_abi_def, AllCaseEqs()]) >>
  gvs[Once value_has_type_def]
QED

Theorem entry_source_bulk_owned_endpoint:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) = DecDynArray ei abi_sz mem_sz F maxn /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    root_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s /\
  entry_scratch_ready sites b cap s ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_decode_path ctx fn s t /\ entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
    entry_scratch_ready sites b cap t /\ alloca_inv t /\
    abi_alloca_history (fn_insts fn) t /\ alloca_frontier_inv ctx fn site t /\
    entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    abi_encoder_registered_effect child_sites [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all source_bulk_values >> strip_tac >>
  drule_all entry_bulk_owned_core >> simp[]
QED
