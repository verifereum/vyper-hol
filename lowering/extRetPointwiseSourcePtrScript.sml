Theory extRetPointwiseSourcePtr
Ancestors bodyPtrDefs abiEncoderSourceProducer abiEncoderSourceAggregate
  abiEncoderOpenInput abiEncoderSourceTransport abiEncoderProps
  vyperABI vyperTyping valueEncoding venomExecSemantics

(* The representation type is uniform; its value representative may depend
   on the memory. No source allocation-capacity bound is asserted here. *)
Theorem ptr_mem_ok_pointwise_open_input:
  abi_enc_plan (get_tenv cx) ty ei /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  ptr_mem_ok cx ty v op G tn s /\ eval_operand op s = SOME w ==>
  ?ct. source_rep (get_tenv cx) ty ei ct /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    ?rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
         abi_encoder_open_input ei ct rv (w2n w) (type_memory_size tv) mem
Proof
  strip_tac >> drule (cj 1 abi_encoder_uniform_source) >> strip_tac >>
  qexists `ct` >> simp[] >> rpt strip_tac >>
  irule source_rep_transport >> simp[] >>
  qexists `v` >> simp[] >>
  gvs[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_val_ok_pointwise_open_input:
  abi_enc_plan (get_tenv cx) ty ei /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  ptr_val_ok cx ty v op G tn s /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  ?ct. source_rep (get_tenv cx) ty ei ct /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    ?rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
         abi_encoder_open_input ei ct rv (w2n w) (type_memory_size tv) mem
Proof
  strip_tac >> irule ptr_mem_ok_pointwise_open_input >>
  gvs[ptr_val_ok_def] >> metis_tac[]
QED
