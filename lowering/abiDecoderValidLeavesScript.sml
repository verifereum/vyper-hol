(* All primitive source types close the actual-source recursive API. *)
Theory abiDecoderValidLeaves
Ancestors
  abiDecoderValidPrefix abiDecoderValidBytesCorrect abiDecoderValidContract
  compileEnv vyperABI vyperValue contractABI list

Theorem abi_decoder_valid_base_cases:
  !bt. ~is_dynamic (vyper_to_abi_type env (BaseT bt)) \/
    ?n. bt = BytesT (Dynamic n) \/ bt = StringT n
Proof
  Cases >> simp[vyper_to_abi_type_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[]
QED

Theorem abi_decoder_valid_correct_base:
  abi_decoder_valid_correct ce env sf (BaseT bt) (BaseTV bt)
Proof
  mp_tac (Q.SPEC `bt` abi_decoder_valid_base_cases) >>
  disch_then (DISJ_CASES_THEN2 assume_tac (qx_choose_then `n` assume_tac))
  >- (irule abi_decoder_valid_correct_static >> first_assum ACCEPT_TAC) >>
  irule abi_decoder_valid_correct_bytestring >> qexists_tac `n` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_decoder_valid_correct_flag:
  abi_decoder_valid_correct ce env sf (FlagT nsid) (FlagTV n)
Proof
  irule abi_decoder_valid_correct_static >> simp[vyper_to_abi_type_def]
QED
