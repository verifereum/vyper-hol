(* Indexed canonical child addresses and independent observable fields. *)
Theory entryReachBodyCanonicalChildAddress
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyExactArrayLoop abiDecoderArraySetupInputs abiDecoderLoopSetup
  abiDecoderArrayInvariant
  abiDecoderIndexedAddress abiDecoderDynamic abiDecoderContract abiDecoderFrame
  abiDecoderCoherence abiDecoderTypedContract abiDecodeRanges abiDecoderReentry
  abiEncoder emitHelper emitHelperProps compileEnv exprLoweringProps
  venomState venomExecSemantics venomExecProofs venomInst
  valueEncoding valueEncodingProps vyperABI vyperValue vyperTyping
  contractABI words list rich_list arithmetic

Theorem entry_address_step_fields[local]:
  MEM i.inst_opcode [MLOAD; ADD; MUL; CALLDATALOAD] /\ step_inst_base i s = OK t ==>
  entry_loop_fields s t
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, exec_pure2_def, AllCaseEqs()] >> strip_tac >>
  gvs[entry_loop_fields_def, update_var_def]
QED

Theorem entry_address_sequence_fields[local]:
  !code s t.
  EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; MUL; CALLDATALOAD]) code /\
  run_inst_seq code s = OK t ==> entry_loop_fields s t
Proof
  Induct >- simp[run_inst_seq_def, entry_loop_fields_def] >> rpt gen_tac >>
  simp_tac (srw_ss()) [run_inst_seq_def, EVERY_DEF, AllCaseEqs(), Excl "MEM"] >> strip_tac >>
  `MEM h.inst_opcode [MLOAD; ADD; MUL; CALLDATALOAD]` by simp[] >>
  drule_all entry_address_step_fields >> strip_tac >>
  rename1 `run_inst_seq code middle = OK t` >>
  first_x_assum (qspecl_then [`middle`,`t`] mp_tac) >>
  gvs[MEM, entry_loop_fields_def]
QED

Theorem entry_address_setup_opcodes[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di abi_sz mem_sz st =
    (ops,st') ==>
  EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; MUL; CALLDATALOAD]) (emitted_insts st st')
Proof
  Cases_on `dec_info_needs_offset di` >>
  simp[abi_decode_array_element_setup_def, compile_abi_decode_dyn_elem_ptr_def,
    abi_decode_indexed_address_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem entry_address_setup_fields[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w) di abi_sz mem_sz st =
    (ops,st') /\ run_inst_seq (emitted_insts st st') s = OK t ==>
  entry_loop_fields s t
Proof
  strip_tac >> drule entry_address_setup_opcodes >> strip_tac >>
  drule_all entry_address_sequence_fields >> simp[]
QED

Theorem entry_canonical_dynamic_child_address:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ty) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb +
      abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ entry_loop_fields s t /\
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (EL j avs) (EL j xs) /\
    mem_bytes_at (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)
      (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)))
      (abi_decode_source CALLDATALOAD t) = enc (vyper_to_abi_type env ty) (EL j avs) /\
    sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j < dimword (:256) /\
    sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j +
      LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) <= sb +
      LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) /\
    d+32+j*type_memory_bytes ce ty < dimword (:256) /\
    d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty <=
      d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
    abi_embedded_static_size ce.ce_struct_fields ty <=
      LENGTH (enc (vyper_to_abi_type env ty) (EL j avs))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `?pre av post. avs = pre ++ av::post /\ LENGTH pre = j` by
    (qexistsl_tac [`TAKE j avs`,`EL j avs`,`DROP (SUC j) avs`] >>
     simp[LENGTH_TAKE, MIN_DEF] >>
     mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> metis_tac[]) >>
  `?vpre v vpost. xs = vpre ++ v::vpost /\ LENGTH vpre = j` by
    (qexistsl_tac [`TAKE j xs`,`EL j xs`,`DROP (SUC j) xs`] >>
     simp[LENGTH_TAKE, MIN_DEF] >>
     mp_tac (Q.ISPEC `xs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> metis_tac[]) >>
  gvs[Excl "enc_def", EL_APPEND_EQN] >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH pre = LENGTH vpre` by decide_tac >>
  drule_all abi_decoder_dynarray_dynamic_setup >> strip_tac >>
  drule_all entry_address_setup_fields >> strip_tac >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
      (ListV (pre ++ av::post))) < dimword (:256) /\
   d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by
    fs[abi_decoder_ranges_def] >>
  drule_all abi_decoder_dynarray_child_source >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_decoder_address_frame_source >>
  disch_then (qspec_then `CALLDATALOAD` assume_tac) >>
  qpat_x_assum `LENGTH pre = LENGTH vpre` kall_tac >>
  qexists_tac `t` >>
  full_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND, AC ADD_ASSOC ADD_COMM] >>
  rpt conj_tac >> decide_tac
QED

(* Interface check: the child is itself a dynamic array, not a word leaf. *)
Theorem entry_canonical_nested_array_address[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
    (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
    (type_memory_bytes ce (ArrayT ty (Dynamic inner))) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) /\
  abi_decoder_metadata ce env (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic inner))) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    d (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) b cap s /\
  mem_bytes_at sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ entry_loop_fields s t /\
    abi_decoder_metadata ce env (ArrayT ty (Dynamic inner)) (ArrayTV tv (Dynamic inner))
      (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic inner)))
      (EL j avs) (EL j xs) /\
    mem_bytes_at
      (sb + abi_array_child_offset NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner))) avs j)
      (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic inner))) (EL j avs)))
      (abi_decode_source CALLDATALOAD t) =
      enc (vyper_to_abi_type env (ArrayT ty (Dynamic inner))) (EL j avs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_canonical_dynamic_child_address >>
  strip_tac >> qexists_tac `t` >> asm_rewrite_tac []
QED
