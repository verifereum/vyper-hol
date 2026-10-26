(* Canonical fixed-array bytes are the repeated-type tuple encoding. *)
Theory abiDecoderFixedInputs
Ancestors
  abiDecoderPreObservations abiDecoderFixedMembers abiDecoderMembers abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiCanonicalArrays
  compileEnv valueEncoding vyperABI vyperValue contractABI venomState words list rich_list

Theorem abi_decoder_fixed_array_inputs:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) ==>
  ?avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\ LENGTH vs = n /\
    abi_decoder_members ce env sf (REPLICATE n ty) (REPLICATE n tv) avs vs /\
    type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty)) /\
    abi_decoder_ranges opc hi src dst sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs)))
      d (SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))) b cap initial /\
    mem_bytes_at sb
      (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs)))
      (abi_decode_source opc initial) =
        enc (Tuple (MAP (vyper_to_abi_type env) (REPLICATE n ty))) (ListV avs) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var hi
Proof
  strip_tac >> drule abi_decoder_pre_observations >> strip_tac >>
  drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) = SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))`
    by simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  gvs[Once vyper_to_abi_type_def, canonical_array_tuple, map_replicate, Excl "enc_def"] >>
  metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_FIXED_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI fixed-array inputs not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderFixedInputs");
