(* Open-array prefix preservation across a restricted initializer scratch frame. *)
Theory abiEncoderSharedArrayInitFrame
Ancestors
  abiEncoderSharedArrayInput abiEncoderSharedContract abiEncoderOpenInput
  abiEncoderArrayPrefix abiScratchSubset abiDecoderFootprint abiDecoderAllocation
  compileEnv valueEncoding contractABI venomState pred_set list arithmetic

Theorem abi_encoder_shared_array_prefix_scratch:
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual /\
  first <= lo /\ hi <= last ==>
  abi_encoder_array_prefix ty avs j d actual.vs_memory
Proof
  strip_tac >> irule abi_encoder_open_array_prefix_output_frame >>
  conj_tac >- (drule abi_encoder_shared_array_input_facts >> strip_tac >>
    irule abi_encoder_structural_list_layout >> simp[]) >>
  qexistsl_tac [`abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial`,`initial`,`sz`] >>
  asm_simp_tac bool_ss [] >> conj_tac >- fs[abi_encoder_shared_input_def] >>
  irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >>
  fs[abi_encoder_shared_input_def, SUBSET_DEF, abi_decoder_ids_def] >> decide_tac
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array init frame admission, axiom or hypothesis"
  end) [abi_encoder_shared_array_prefix_scratch];
