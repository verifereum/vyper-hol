(* Operational execution of a dynamic bytes array at an outer child address. *)
Theory entryReachBodyNestedBytesExecution
Ancestors
  entryReachBodyNestedOwnedPath entryReachBodyOwnedBytesArray
  entryReachBodyNestedScratchTransport
  entryReachBodyOperationalPath entryReachBodySequenceObservations
  entryReachBodyExactArrayLoop abiEncoderRegisteredEffect
  abiDecoderDynamicLoopSetup abiDecoderTypedContract abiDecoderContract
  compileEnv venomState finite_map words pred_set list arithmetic

Theorem nested_address_effect[local]:
  abi_decoder_address_frame next s u /\ entry_loop_fields s u ==>
  abi_encoder_registered_effect ids outs s u
Proof
  simp[abi_decoder_address_frame_def, entry_loop_fields_def,
       abi_encoder_registered_effect_def]
QED

Theorem entry_nested_owned_bytes_execution:
  ity = ArrayT ty (Dynamic inner) /\ itv = ArrayTV tv (Dynamic inner) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ity) (abi_embedded_static_size ce.ce_struct_fields ity)
    (type_memory_bytes ce ity) st = (ops,middle) /\
  abi_decoder_coherent ce env sf (ArrayT ity (Dynamic outer)) (ArrayTV itv (Dynamic outer)) /\
  abi_decoder_metadata ce env (ArrayT ity (Dynamic outer)) (ArrayTV itv (Dynamic outer))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ity) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
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
    b <= q /\ q+32 <= b+cap) /\
  EL j avs = ListV iavs /\ EL j xs = ArrayV (DynArrayV ixs) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  is_dynamic (vyper_to_abi_type env ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\ EVERY (val_wf tv) ixs /\
  LENGTH ixs = LENGTH iavs /\ LENGTH ixs <= inner /\
  inner < dimword (:256) /\ n < dimword (:256) /\
  type_to_abi_dec_info ce.ce_struct_fields ce ity =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner) middle = ((),final) /\
  fn_has_code middle final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  (!i. MEM i (emitted_insts middle loop_st) ==> MEM i (fn_insts fn)) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  oid <> header_st.cs_next_id /\ cid <> header_st.cs_next_id ==>
  ?t q. val_in_memory itv (EL j xs) (d+32+j*type_memory_bytes ce ity) t.vs_memory /\
    entry_decode_path ctx fn s t /\ entry_loop_fields s t /\ ~t.vs_halted /\
    t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ fresh_vars_wrt limit_st t /\
    entry_owned_loop_resources ctx fn site header_st.cs_next_id q oid root extent
      (d+32+j*type_memory_bytes ce ity) (type_memory_bytes ce ity) t /\
    abi_encoder_registered_effect {header_st.cs_next_id}
      [(d+32+j*type_memory_bytes ce ity,type_memory_bytes ce ity)] s t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (if FLOOKUP s.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = s.vs_alloca_next+32 else t.vs_alloca_next = s.vs_alloca_next) /\
    entry_nested_scratch_ready header_st.cs_next_id b cap t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_nested_owned_initializer_boundary >>
  disch_then (qx_choose_then `u` (qx_choose_then `q` strip_assume_tac)) >>
  suspend "inner"
QED

Resume entry_nested_owned_bytes_execution[inner]:
  `st.cs_next_var <= middle.cs_next_var` by
    (drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     simp_tac bool_ss []) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _`,
     `abi_decoder_coherent _ _ _ (ArrayT _ (Dynamic outer)) _`,
     `abi_decoder_metadata _ _ (ArrayT _ (Dynamic outer)) _ _ _ _`,
     `abi_decoder_ranges _ _ src dst _ _ _ _ _ _ s`,
     `mem_bytes_at sb _ _ = _`, `eval_operand ip s = _`, `mload _ s = _`,
     `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ s`,
     `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ u`] >>
  gvs[Excl "enc_def", IgnAsm `type_memory_bytes ce ty = _`] >>
  `LENGTH ixs <= inner` by decide_tac >>
  qpat_assum `type_memory_bytes ce ty = _`
    (fn th => drule_all (REWRITE_RULE [th] entry_owned_canonical_bytes_array_execution)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  suspend "compose"
QED
Resume entry_nested_owned_bytes_execution[compose]:
  `eval_operand (FST ops) t = SOME (n2w j) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (if FLOOKUP s.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = s.vs_alloca_next+32 else t.vs_alloca_next = s.vs_alloca_next)` by
    suspend "producer_frames" >>
  `entry_nested_scratch_ready header_st.cs_next_id b cap t` by suspend "scratch_ready" >>
  `entry_decode_path ctx fn s t` by metis_tac[entry_decode_path_trans] >>
  `entry_loop_fields s t` by
    metis_tac[entryReachBodyRegisteredChildTheory.entry_registered_fields_trans] >>
  `abi_encoder_registered_effect {header_st.cs_next_id}
     [(d+32+j*type_memory_bytes ce (ArrayT ty (Dynamic inner)),
       type_memory_bytes ce (ArrayT ty (Dynamic inner)))] s u` by
    metis_tac[nested_address_effect] >>
  qexistsl_tac [`t`,`q`] >>
  simp[Excl "enc_def"] >>
  qpat_assum `abi_encoder_registered_effect _ _ s u` mp_tac >>
  qpat_assum `abi_encoder_registered_effect _ _ u t` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM] >>
  metis_tac[abi_encoder_registered_effect_trans]
QED
Resume entry_nested_owned_bytes_execution[producer_frames]:
  qpat_x_assum `abi_decoder_address_frame _ s u` mp_tac >>
  qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
  qpat_x_assum `eval_operand (FST ops) u = _` mp_tac >>
  qpat_x_assum `abi_decoder_operand_live middle.cs_next_var (FST ops)` mp_tac >>
  qpat_x_assum `!op w. abi_decoder_operand_live middle.cs_next_var op /\ _ ==> _` mp_tac >>
  qpat_x_assum `!id. id <> header_st.cs_next_id ==> _` mp_tac >>
  qpat_x_assum `if FLOOKUP u.vs_allocas _ = NONE then _ else _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [abi_decoder_address_frame_def] >> rpt strip_tac >>
  metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]
QED
Resume entry_nested_owned_bytes_execution[scratch_ready]:
  `entry_nested_scratch_ready header_st.cs_next_id b cap s` by
    simp[entry_nested_scratch_ready_def, Excl "enc_def"] >>
  `FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (q,32)` by
    fs[entryReachBodyOwnedLoopTheory.entry_owned_loop_resources_def, Excl "enc_def"] >>
  irule entry_nested_scratch_ready_transition >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qpat_x_assum `entry_array_init_resources _ _ _ _ _ (_,_,_,_,_,_,_,_,u)` mp_tac >>
  qpat_x_assum `abi_decoder_address_frame _ s u` mp_tac >>
  qpat_x_assum `if FLOOKUP s.vs_allocas _ = NONE then _ else _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [entryReachBodyCanonicalBytesArrayTheory.entry_array_init_resources_def,
    abi_decoder_address_frame_def] >> rpt strip_tac >> gvs[Excl "enc_def"]
QED
Finalise entry_nested_owned_bytes_execution
