(* All primitive source types close the physical decoder execution contract. *)
Theory abiScratchDecoderLeaves
Ancestors
  abiScratchDecoderWord abiScratchDecoderBytes abiScratchDecoderContract
  exprLowering compileEnv vyperAST list

Theorem abi_scratch_decoder_base_shape:
  !bt. (?clamp. type_to_abi_dec_info
    (sf:string |-> (string # vyperAST$type # num) list) ce (BaseT bt) = DecPrimWord clamp) \/
    (?n. bt = BytesT (Dynamic n) \/ bt = StringT n)
Proof
  Cases >> simp[type_to_abi_dec_info_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def]
QED

Theorem abi_scratch_decoder_base:
  abi_scratch_decoder ce env sf (BaseT bt) tv
Proof
  mp_tac (Q.SPEC `bt` abi_scratch_decoder_base_shape) >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `clamp` assume_tac)
    (qx_choose_then `n` assume_tac))
  >- (irule abi_scratch_decoder_word >> qexists_tac `clamp` >> asm_simp_tac bool_ss []) >>
  irule abi_scratch_decoder_bytestring >> qexists_tac `n` >> asm_simp_tac (srw_ss()) []
QED

Theorem abi_scratch_decoder_flag:
  abi_scratch_decoder ce env sf (FlagT nsid) tv
Proof
  irule abi_scratch_decoder_word >> simp[type_to_abi_dec_info_def]
QED
