(* A static representative is selected once, independently of memory. *)
Theory abiEncoderUniformStaticSource
Ancestors
  abiEncoderSourceWindow abiEncoderOpenInput valueEncodingProps
  vyperABI vyperValue vyperTyping contractABI

Theorem abi_encoder_uniform_static_value_source:
  evaluate_type env ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  ?ct. ~is_dynamic ct /\ static_length ct = type_memory_size tv /\
    !v av sb mem0.
      value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
      val_in_memory tv v sb mem0 ==>
      ?rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
        !mem. val_in_memory tv v sb mem ==>
          abi_encoder_open_input (AbiCopy (type_memory_size tv)) ct rv sb
            (type_memory_size tv) mem
Proof
  strip_tac >> drule_all abi_encoder_uniform_static_source >>
  disch_then (qx_choose_then `ct` strip_assume_tac) >>
  qexists_tac `ct` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!v av sb mem. _` drule_all >>
  disch_then (qx_choose_then `rv` strip_assume_tac) >>
  qexists_tac `rv` >> simp[] >> rpt strip_tac >>
  drule_all val_in_memory_static_abi >> strip_tac >>
  qpat_x_assum `abi_encoder_open_input _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [abi_encoder_open_input_cases]) >>
  irule abiEncoderOpenInputTheory.copy >> gvs[]
QED
