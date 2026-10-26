(* Complete default encoder inputs for every recursively coherent source type.
   Child ABI typing is required only when that child occurs in the value. *)
Theory abiEmptyRecursiveInput
Ancestors
  abiEmptyStructInput abiEmptyAggregateInput abiEmptyInputLeaves abiEmptyInputTransport
  abiDecoderCoherence abiEncoderInput compileEnv exprLowering valueEncoding vyperABI
  contractABI finite_map words list rich_list arithmetic

Theorem abi_empty_base_default_input:
  abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt) /\
  has_type (vyper_to_abi_type env (BaseT bt)) (default_to_abi (BaseTV bt)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT bt))
    (vyper_to_abi_type env (BaseT bt)) (default_to_abi (BaseTV bt))
    0 (type_memory_bytes ce (BaseT bt)) []
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env (BaseT bt))`
  >- (Cases_on `bt` >> gvs[vyper_to_abi_type_def, is_dynamic_def] >>
      FIRST [irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
          (cj 2 abi_empty_bytestring_inputs)) >> simp[abi_empty_memory_observation],
        rename1 `BytesT bound` >> Cases_on `bound` >> gvs[is_dynamic_def] >>
        irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
          (cj 1 abi_empty_bytestring_inputs)) >> simp[abi_empty_memory_observation]]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED

Theorem abi_empty_flag_default_input:
  abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n) /\
  has_type (vyper_to_abi_type env (FlagT nsid)) (default_to_abi (FlagTV n)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (FlagT nsid))
    (vyper_to_abi_type env (FlagT nsid)) (default_to_abi (FlagTV n))
    0 (type_memory_bytes ce (FlagT nsid)) []
Proof
  strip_tac >> irule abi_empty_coherent_static_input >>
  simp[abi_empty_memory_observation] >>
  fs[abi_decoder_coherent_flag_iff, vyper_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_empty_array_default_input:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_header ce env (ArrayT ty bound) (ArrayTV tv bound) /\
  (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) 0 (type_memory_bytes ce ty) []) /\
  has_type (vyper_to_abi_type env (ArrayT ty bound)) (default_to_abi (ArrayTV tv bound)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (ArrayT ty bound))
    (vyper_to_abi_type env (ArrayT ty bound)) (default_to_abi (ArrayTV tv bound))
    0 (type_memory_bytes ce (ArrayT ty bound)) []
Proof
  strip_tac >> Cases_on `bound`
  >- (irule abi_empty_fixed_default_input >> simp[abi_decoder_coherent_array_iff]) >>
  irule abi_empty_dynamic_array_input >> simp[abi_empty_memory_observation] >>
  drule abi_decoder_coherent_header >> simp[]
QED

Theorem abi_empty_recursive_default_input:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) 0 (type_memory_bytes ce ty) []
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- (rpt strip_tac >> irule abi_empty_base_default_input >>
      simp[abi_decoder_coherent_base_iff])
  >- (rpt strip_tac >> irule abi_empty_flag_default_input >>
      simp[abi_decoder_coherent_flag_iff])
  >- (rpt strip_tac >> irule abi_empty_array_default_input >> simp[])
  >- (rpt strip_tac >> irule abi_empty_tuple_default_input >>
      fs[abi_decoder_coherent_tuple_iff, LIST_REL_CONJ] >>
      RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  rpt strip_tac >> irule abi_empty_struct_default_input >>
  asm_rewrite_tac[] >> qexists_tac `fields` >> simp[]
QED

Theorem abi_empty_default_initialized_input:
  abi_decoder_coherent ce env sf ty tv /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  mem_bytes_at p (type_memory_bytes ce ty) mem = REPLICATE (type_memory_bytes ce ty) 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) p (type_memory_bytes ce ty) mem
Proof
  strip_tac >> drule_all abi_empty_recursive_default_input >> strip_tac >>
  irule abi_empty_input_relocate >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_RECURSIVE_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty recursive input not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyRecursiveInput");
