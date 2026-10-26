(* Fixed arrays execute the shared complex decoder and recover sparse values. *)
Theory abiDecoderCorrectFixed
Ancestors
  abiDecoderCorrect abiDecoderFixedInputs abiDecoderFixedMemory abiDecoderComplexExecute
  abiDecoderMemberInfos abiDecoderEffect abiDecoderCoherence abiDecoderReentry
  abiDecoderTypedContract abiDecoderContract fragExec compileEnv valueEncoding
  vyperABI vyperValue venomState words list rich_list

Theorem abi_decoder_correct_fixed_array:
  abi_decoder_correct ce env sf ty tv ==>
  abi_decoder_correct ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_fixed_array_inputs >> strip_tac >> gvs[Excl "enc_def"] >>
  (`LIST_REL (abi_decoder_correct ce env sf) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)`
    by simp[LIST_REL_REPLICATE_same] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
    (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `tys` |-> `REPLICATE (LENGTH vs) ty`,
      `tvs` |-> `REPLICATE (LENGTH vs) tv`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
      abi_decoder_complex_execute)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `tuple_in_memory vs (REPLICATE (LENGTH vs) tv) d actual.vs_memory` >>
  `val_in_memory (ArrayTV tv (Fixed (LENGTH vs)))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d actual.vs_memory`
    by (irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED
