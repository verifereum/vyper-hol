(* Both array constructors satisfy the precise recursive API.
   TOP-LEVEL: abi_scratch_encoder_array proves the actual complete constructor;
   static and dynamic corollaries expose the two compiler branches separately. *)
Theory abiScratchEncoderArray
Ancestors
  abiScratchArrayRun abiScratchEncoderContract abiEncoderInput abiDecoderReentry
  abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI venomState words list

Theorem abi_scratch_encoder_array:
  (if active then abi_scratch_encoder ei else abi_encoder_static_leaf ei) ==>
  abi_scratch_encoder (AbiDynArray ei asz msz active)
Proof
  strip_tac >> simp_tac bool_ss [abi_scratch_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  qpat_x_assum `at = Array NONE ct` SUBST_ALL_TAC >>
  qpat_x_assum `av = ListV values` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`final` |-> `end_st`, `ty` |-> `ct:abi_type`, `avs` |-> `values:abi_value list`,
    `output_size` |-> `LENGTH (enc (Array NONE ct) (ListV values))`] abi_scratch_array_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_encoder_array_dynamic:
  abi_scratch_encoder ei ==> abi_scratch_encoder (AbiDynArray ei asz msz T)
Proof
  strip_tac >> irule (Q.INST [`active` |-> `T`] abi_scratch_encoder_array) >> simp[]
QED

Theorem abi_scratch_encoder_array_static:
  abi_encoder_static_leaf ei ==> abi_scratch_encoder (AbiDynArray ei asz msz F)
Proof
  strip_tac >> irule (Q.INST [`active` |-> `F`] abi_scratch_encoder_array) >> simp[]
QED
