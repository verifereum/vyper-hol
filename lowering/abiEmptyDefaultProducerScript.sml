(* Actual Empty execution establishes the recursive ABI source input.
   Count-only roots require only their initialized count word. *)
Theory abiEmptyDefaultProducer
Ancestors
  abiEmptyRecursiveInput abiEmptyInput abiEmptyAllocate abiEmptySize abiEmptyEffect
  abiEmptyProducer abiBuiltinAllocation abiDecoderCoherence abiCallerCoherence abiEncoderInput
  compileEnv builtinSimple exprLowering exprLoweringProps valueEncoding vyperABI compileVyper
  vyperTypeSystem vyperValue vyperContext venomState venomExecSemantics finite_map words list
  arithmetic

Theorem abi_empty_count_default_input:
  abi_decoder_coherent ce env sf ty tv /\
  (is_bytestring_type ty \/ (case ty of ArrayT _ (Dynamic _) => T | _ => F)) /\
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) p (type_memory_bytes ce ty) mem
Proof
  strip_tac >> Cases_on `ty` >> gvs[is_bytestring_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
      FIRST [gvs[abi_decoder_coherent_string_iff] >>
          irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
            (cj 2 abi_empty_bytestring_inputs)) >> simp[],
        rename1 `BytesT bound` >> Cases_on `bound` >> gvs[is_bytestring_type_def] >>
        gvs[abi_decoder_coherent_bytes_iff] >>
        irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
          (cj 1 abi_empty_bytestring_inputs)) >> simp[]]) >>
  rename1 `ArrayT child bound` >> Cases_on `bound` >> gvs[] >>
  gvs[abi_decoder_coherent_array_iff] >>
  irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
    abi_empty_dynamic_array_input) >> simp[] >>
  drule abi_decoder_coherent_header >> simp[]
QED

Theorem abi_empty_default_producer:
  abi_decoder_coherent ce env sf ty tv /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  length_only = (is_bytestring_type ty \/
    (case ty of ArrayT _ (Dynamic _) => T | _ => F)) /\
  compile_builtin_empty_complex (type_memory_bytes ce ty) length_only st = (buf,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ty)) /\
  type_memory_bytes ce ty < dimword (:256) /\
  p+abi_empty_initialized_bytes (type_memory_bytes ce ty) length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand buf.buf_operand actual = SOME (n2w p) /\
    buf.buf_size = type_memory_bytes ce ty /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) p (type_memory_bytes ce ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p
      (abi_empty_initialized_bytes (type_memory_bytes ce ty) length_only) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ty) initial) actual /\
    inst_extends st final
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_empty_complex_execute >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK actual` >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
     (default_to_abi tv) p (type_memory_bytes ce ty) actual.vs_memory` by
    (Cases_on `length_only`
     >- (irule abi_empty_count_default_input >> fs[abi_empty_initialized_bytes_def]) >>
     drule abi_empty_round_coherent >> strip_tac >>
     irule abi_empty_default_initialized_input >> fs[]) >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED
