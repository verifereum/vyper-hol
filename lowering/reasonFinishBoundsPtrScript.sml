(* Natural allocation bounds discharge the shared checked finish arithmetic. *)
Theory reasonFinishBoundsPtr
Ancestors reasonResourcesPtr abiEncoderRounding contractABI words arithmetic
  vfmConstants valueEncoding exprSimProps integer
Libs intLib wordsLib

Theorem reason_finish_capacity_bounds:
  32 + 32 * word_size l <= m /\ 64 + m < dimword (:256) /\
  w2n (payload_addr:bytes32) + (32+m) < dimword (:256) /\
  w2n (outer_addr:bytes32) + (64+m) < dimword (:256) ==>
  32 <= m /\ w2n (32w + n2w l : bytes32) <= m /\
  w2n (((n2w l:bytes32) + 31w) && i2w (-32)) + 32 <= m /\
  w2n payload_addr + 32 < dimword (:256) /\
  w2n (payload_addr + 32w) +
    w2n (((n2w l:bytes32) + 31w) && i2w (-32)) < dimword (:256) /\
  w2n outer_addr + 28 < dimword (:256) /\
  28 + w2n (4w + (32w + (32w + (((n2w l:bytes32) + 31w) && i2w (-32))))) <= 64+m
Proof
  strip_tac >>
  `l <= 32 * word_size l` by simp[le_word_size_mul] >>
  `l+31 < dimword (:256)` by decide_tac >>
  `((n2w l:bytes32) + 31w) && i2w (-32) = n2w (32 * word_size l)` by
    (drule abi_encoder_round_ceil32 >>
     `i2w (-32) = (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w:bytes32)` by EVAL_TAC >>
     strip_tac >>
     once_rewrite_tac[wordsTheory.WORD_AND_COMM] >>
     once_rewrite_tac[wordsTheory.WORD_ADD_COMM] >>
     fs[contractABITheory.ceil32_def, word_size_def]) >>
  fs[wordsTheory.dimword_def] >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w,
       wordsTheory.w2n_add_2] >>
  rpt conj_tac >> dep_rewrite.DEP_REWRITE_TAC[arithmeticTheory.LESS_MOD] >> decide_tac
QED
