(* Choose ABI representatives before varying unread or tainted memory. *)
Theory abiEncoderSourceRobust
Ancestors
  abiEncoderUniformValueSource abiEncoderWindowSource abiEncoderProps compileEnv
  abiEncoderLiveSource abiEncoderSourceProducer abiEncoderSourceAggregate
  abiEncoderSourceWindow abiEncoderWindow abiEncoderOpenInput bodyPtrDefs
  vyperABI vyperABIValid vyperTyping vyperValue valueEncoding loweringPosts
  contractABI list arithmetic

Theorem abi_encoder_source_window_robust:
  abi_enc_plan env ty ei /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tainted initial_mem mem ==>
    val_in_memory tv v sb mem) ==>
  ?ct rv.
    contractABI$enc ct rv =
      contractABI$enc (vyper_to_abi_type env ty) av /\
    LENGTH (contractABI$enc ct rv) <= vyper_abi_size_bound env ty /\
    !mem. mem_agree_outside tainted initial_mem mem ==>
      abi_encoder_window_input ei ct rv sb (val_footprint tv v) mem
Proof
  strip_tac >>
  drule_all (cj 1 vyperABIValidTheory.vyper_to_abi_enc_le_size_bound) >>
  strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- (`val_in_memory tv v sb initial_mem` by
        (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      drule (cj 1 abi_encoder_uniform_value_source) >>
      disch_then (qx_choose_then `ct` strip_assume_tac) >>
      qpat_x_assum `!tv v av sb mem0. _` drule_all >>
      disch_then (qx_choose_then `rv` strip_assume_tac) >>
      qexistsl_tac [`ct`, `rv`] >> simp[] >> rpt strip_tac >>
      irule abi_encoder_open_input_window >> metis_tac[]) >>
  drule_all abi_source_non_nominal_forms >> strip_tac >> gvs[]
  >~ [`abi_enc_plan env (BaseT (BytesT (Dynamic n))) ei`]
  >- (`ei = AbiBytestring n` by
        gvs[Once abi_enc_plan_cases, is_word_type_def, vyper_to_abi_type_def,
            vyper_base_to_abi_type_def, is_dynamic_def] >>
      gvs[] >> qexistsl_tac [`Bytes NONE`, `contractABI$BytesV bs`] >>
      simp[val_footprint_def, enc_def] >> rpt strip_tac >>
      irule (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
               abi_encoder_window_bytes_source) >>
      qexistsl_tac [`env`, `BaseTV (BytesT (Dynamic n))`,
                    `vyperValue$BytesV bs`] >>
      simp[vyper_to_abi_def] >> metis_tac[]) >>
  `ei = AbiBytestring n` by
    gvs[Once abi_enc_plan_cases, is_word_type_def, vyper_to_abi_type_def,
        vyper_base_to_abi_type_def, is_dynamic_def] >>
  gvs[] >>
  qexistsl_tac [`String`, `contractABI$BytesV (MAP n2w_o_ORD str)`] >>
  simp[val_footprint_def, enc_def] >> rpt strip_tac >>
  `vyper_to_abi env (BaseT (StringT n)) (StringV str) =
     SOME (contractABI$BytesV (MAP n2w_o_ORD str))` by
    simp[vyper_to_abi_def] >>
  `val_in_memory (BaseTV (StringT n)) (StringV str) sb mem` by
    metis_tac[] >>
  drule_all abi_encoder_window_string_source >> simp[ADD_COMM]
QED
