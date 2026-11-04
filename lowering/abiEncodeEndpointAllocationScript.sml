Theory abiEncodeEndpointAllocation
Ancestors
  abiCallerAllocation abiEncoderSharedContract abiDecoderAllocation abiDecoderFrame
  abiDecoderFootprint abiDecoderReentry venomMemDefs venomState compileEnv
  words finite_map pred_set arithmetic list

Theorem abi_encode_owned_shared_input:
  alloca_inv s /\
  abi_encoder_open_input ei at av sb source_cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  LENGTH (enc at av) <= output_size /\
  sb+source_cap < dimword (:256) /\ d+output_size < dimword (:256) /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,source_size) /\
  source_base <= sb /\ sb+source_cap <= source_base+source_size /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  output_base <= d /\ d+output_size <= output_base+output_cap /\
  source_id <> output_id /\
  ~(source_id IN abi_decoder_ids first last) /\
  ~(output_id IN abi_decoder_ids first last) /\ s.vs_alloca_next <= cap ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,0,cap) s
Proof
  strip_tac >>
  `abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) 0 cap s)` by
    (irule abi_caller_allocation_scratch >> simp[] >>
     qexistsl [`source_size`, `source_id`, `source_base`] >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) 0 cap s)` by
    (irule abi_caller_allocation_scratch >> simp[] >>
     qexistsl [`output_cap`, `output_id`, `output_base`] >> simp[]) >>
  drule_all abi_caller_allocation_separate >> strip_tac >>
  simp[abi_encoder_shared_input_def, venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_encode_empty_source_shared_input:
  alloca_inv s /\
  abi_encoder_open_input ei at av sb 0 s.vs_memory /\
  abi_footprint_disjoint sb 0
    (abi_decoder_child_scratch (abi_decoder_ids first last) 0 cap s) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  LENGTH (enc at av) <= output_size /\ sb < dimword (:256) /\
  d+output_size < dimword (:256) /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  output_base <= d /\ d+output_size <= output_base+output_cap /\
  ~(output_id IN abi_decoder_ids first last) /\ s.vs_alloca_next <= cap ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,0)
    (d,output_size) (first,last,0,cap) s
Proof
  strip_tac >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) 0 cap s)` by
    (irule abi_caller_allocation_scratch >> simp[] >>
     qexistsl [`output_cap`, `output_id`, `output_base`] >> simp[]) >>
  simp[abi_encoder_shared_input_def, venomMemDefsTheory.regions_disjoint_def,
       abi_footprint_disjoint_def]
QED
