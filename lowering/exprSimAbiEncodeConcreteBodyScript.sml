Theory exprSimAbiEncodeConcreteBody
Ancestors
  exprSimAbiEncodeConcreteComplex exprSimAbiEncodeConcreteLeaves
  exprSimAbiEncodeNoBlockSafety exprSimAbiEncodeNoBlockStructure
  exprSimAbiEncodeConcreteWrappers abiEncoder emitHelperProps
  exprLoweringProps compileEnv fragExec list rich_list abiEncoderAppend exprSimAbiGasBridge

Theorem abi_encode_concrete_metadata[local]:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  st.cs_blocks = en.cs_blocks ==>
  inst_extends st en /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)
Proof
  strip_tac >>
  `cs_extends st en` by metis_tac[cs_extends_abi_encode] >>
  conj_tac
  >- (fs[cs_extends_def, inst_extends_def] >>
      gvs[] >> fs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  mp_tac (cj 2 enc_straight_encoder_mutual) >>
  simp_tac bool_ss [enc_straight_action_def] >>
  disch_then drule >> strip_tac >>
  fs[frag_code_def, emitted_blocks_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem abi_encode_word_concrete_contract:
  abi_encode_concrete_contract AbiPrimWord
Proof
  simp_tac bool_ss [abi_encode_concrete_contract_def] >> rpt strip_tac >>
  drule_all abi_encode_word_concrete >> strip_tac >>
  drule_all abi_encode_concrete_metadata >> strip_tac >>
  qexists_tac `r` >> simp_tac bool_ss [abi_encode_concrete_result_def] >>
  asm_rewrite_tac[]
QED

Theorem abi_encode_bytes_concrete_contract:
  abi_encode_concrete_contract (AbiBytestring maxlen)
Proof
  simp_tac bool_ss [abi_encode_concrete_contract_def] >> rpt strip_tac >>
  drule_all abi_encode_bytes_concrete >> strip_tac >>
  drule_all abi_encode_concrete_metadata >> strip_tac >>
  qexists_tac `r` >> simp_tac bool_ss [abi_encode_concrete_result_def] >>
  asm_rewrite_tac[]
QED

Theorem abi_encode_copy_concrete_contract:
  abi_encode_concrete_contract (AbiCopy sz)
Proof
  simp_tac bool_ss [abi_encode_concrete_contract_def] >> rpt strip_tac >>
  drule_all abi_encode_copy_concrete >> strip_tac >>
  drule_all abi_encode_concrete_metadata >> strip_tac >>
  qexists_tac `r` >> simp_tac bool_ss [abi_encode_concrete_result_def] >>
  asm_rewrite_tac[]
QED

Theorem abi_encode_concrete_contract_all:
  !ei. abi_encode_concrete_contract ei
Proof
  Induct
  >- ACCEPT_TAC abi_encode_word_concrete_contract
  >- simp[abi_encode_bytes_concrete_contract]
  >- simp[abi_encode_copy_concrete_contract]
  >- (simp_tac bool_ss [abi_encode_concrete_contract_def] >>
      rpt strip_tac >> metis_tac[abi_encode_dyn_array_has_blocks]) >>
  irule abi_encode_complex_concrete_contract >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `(ei,az,ms,dyn)` >>
  simp[]
QED
