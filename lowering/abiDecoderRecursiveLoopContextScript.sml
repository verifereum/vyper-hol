(* Pure code and data premises for the recursive dynamic-array loop. *)
Theory abiDecoderRecursiveLoopContext
Ancestors
  abiDecoderRecursiveArrayIteration abiDecoderArraySetupCode abiDecoderRecursiveLoopInvariant
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract abiDecoderEffect
  abiDecoderProtectedScratch abiDecoderAllocation abiDecoderFrame abiDecoderContract
  abiDecoderCorrect abiDecoderLoop abiDecoderExecution abiDecoderReentry abiDecoderCode
  compileEnv valueEncoding vyperABI vyperValue contractABI venomState venomExecSemantics venomInst
  words list arithmetic

Definition abi_decoder_recursive_loop_compiled_def:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
      hdr exit_lbl hid header_var first last lo hi next limit_st site <=>
    abi_decode_array_element_setup ip src dst opc hi_op (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi_op
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    fn_has_code st end_st func /\ st.cs_current_insts = [] /\
    (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    FST ops = Var (STRING #"%" (toString st.cs_next_var)) /\
    abi_decode_loop_cfg func hdr st.cs_current_bb exit_lbl hid ip src opc
      (STRING #"%" (toString header_var)) (STRING #"%" (toString (header_var+1)))
      (STRING #"%" (toString (header_var+2))) (STRING #"%" (toString (header_var+3))) /\
    (?bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
      bb.bb_instructions = end_st.cs_current_insts ++
        abi_decode_backedge_insts end_st.cs_next_id (STRING #"%" (toString st.cs_next_var))
          (STRING #"%" (toString end_st.cs_next_var)) ip hdr) /\
    first <= lo /\ lo <= site /\ site < st.cs_next_id /\
    lo <= st.cs_next_id /\ st.cs_next_id <= middle.cs_next_id /\
    end_st.cs_next_id <= hi /\ hi <= last /\
    next <= header_var /\ header_var + 4 <= limit_st.cs_next_var /\
    next <= st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var
End

Definition abi_decoder_recursive_loop_data_def:
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi_op ip src dst
      sb d slot b cap next initial <=>
    abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
    abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
      (ListV avs) (ArrayV (DynArrayV vs)) /\
    abi_decoder_ranges opc hi_op src dst sb
      (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
    abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
    abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next ip /\
    eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256)
End

Theorem abi_decoder_recursive_data_facts:
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi_op ip src dst
    sb d slot b cap next initial ==>
  LENGTH avs = LENGTH vs /\ all_have_type tv vs /\ LENGTH vs <= maxn /\
  LENGTH vs < dimword (:256) /\ type_memory_size tv = type_memory_bytes ce ty /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * type_memory_size tv
Proof
  simp_tac bool_ss [abi_decoder_recursive_loop_data_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `LENGTH vs < dimword (:256)` by fs[Once has_type_def] >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  asm_simp_tac bool_ss [Once type_memory_bytes_def]
QED

Theorem abi_decoder_recursive_compiled_facts:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst opc hi_op
    hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_decode_source_opcode opc ==>
  first <= site /\ site < last /\ site < hi /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ next <= end_st.cs_next_var /\
  ?bb. lookup_block hdr func.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0
Proof
  simp_tac bool_ss [abi_decoder_recursive_loop_compiled_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  drule_all abi_decoder_to_buf_code >> simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  `first <= site /\ site < last /\ site < hi /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ next <= end_st.cs_next_var` by decide_tac >>
  asm_simp_tac bool_ss [] >>
  fs[abi_decode_loop_cfg_def] >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decoder_recursive_slot_separation:
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi_op ip src dst
    sb d slot b cap next initial /\
  abi_decoder_budget first last b cap s /\ first <= site /\ site < last /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) ==>
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  (opc = MLOAD ==> sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= slot \/
    slot + 32 <= sb)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `LENGTH vs * type_memory_size tv <= maxn * type_memory_size tv`
    by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  `d + 32 + LENGTH vs * type_memory_size tv <=
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (qpat_x_assum `LENGTH vs * type_memory_size tv <= _` mp_tac >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  conj_tac >- (qpat_x_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b \/ _`
    mp_tac >> strip_tac >> decide_tac) >>
  strip_tac >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= b \/
    b + cap <= sb` by
    (qpat_x_assum `opc = MLOAD ==> _` mp_tac >> asm_simp_tac bool_ss [] >>
     simp_tac bool_ss [abi_footprint_disjoint_def] >>
     disch_then (qspecl_then [`b`, `cap`] mp_tac) >> simp[]) >>
  decide_tac
QED
