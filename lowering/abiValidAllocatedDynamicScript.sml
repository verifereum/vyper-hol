(* Dynamic constructor adapter for the allocation-backed success contract. *)
Theory abiValidAllocatedDynamic
Ancestors
  abiValidAllocatedArrayTraversal abiValidAllocatedBulkReach
  abiValidAllocatedAggregate abiValidAllocatedArraySource
  abiDecoderRecursiveArray abiDecoderRecursiveLoopLayout abiDecoderLoopSetup
  abiDecoderArraySetupCode abiDecoderCoherence abiValidAllocatedMembers
  abiValidAllocatedContract abiDecoderContract
  abiMalformedRecursiveInterface abiMalformedSiteFrame abiMalformedTraversal
  exprLoweringProps exprLowering compileEnv fragExec
  valueEncoding valueEncodingProps vyperABI vyperValue contractABI
  finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_dynamic_array:
  abi_decoder_coherent ce env sf ty tv /\
  abi_valid_allocated_type_contract ce env sf ty tv ==>
  abi_valid_allocated_type_contract ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  rewrite_tac[abi_valid_allocated_type_contract_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (qhdtm_assum `abi_valid_allocated_entry`
        (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
      `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
      `compile_abi_decode_to_buf dst src MLOAD base_op hi
        (DecDynArray (type_to_abi_dec_info sf ce ty)
          (abi_embedded_static_size ce.ce_struct_fields ty)
          (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
        st = ((),en)` by fs[type_to_abi_dec_info_def] >>
      drule_all abi_decoder_recursive_array_code >> strip_tac >>
      `LENGTH xs = L` by
        ( `mem_bytes_at B L s.vs_memory = xs` by
            fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
               Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
          metis_tac[LENGTH_mem_bytes_at]) >>
      `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) (DROP p xs) /\
       abi_to_vyper env (ArrayT ty (Dynamic maxn))
         (dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)) = SOME v` by
        fs[vyper_to_abi_type_def] >>
      drule_all abi_valid_allocated_array_source_view >> strip_tac >>
      cheat) >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) F maxn` by
    fs[type_to_abi_dec_info_def] >>
  metis_tac[abi_valid_allocated_bulk_reach]
QED
