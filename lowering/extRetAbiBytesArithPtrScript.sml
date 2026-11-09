Theory extRetAbiBytesArithPtr
Ancestors
  abiEncoder compileEnv contractABI emitHelper emitHelperProps
  exprLoweringProps fragExec venomInst venomExecSemantics venomLayout
  venomMemProps venomState valueEncoding valueEncodingProps
  list rich_list words byte
Libs
  wordsLib

(* The ceil32 / round-up-mask arithmetic of the ABI bytes encoder, kept from
   the pruned abiBytesExecution theory for the external-return leaves. *)

Theorem abi_bytes_mask_not_31:
  (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32) =
    ~31w
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem abi_bytes_and_complement:
  ∀x m:bytes32. word_and x (word_1comp m) = x - word_and x m
Proof
  rpt gen_tac >>
  `x = word_or (word_and x m) (word_and x (word_1comp m))` by
    simp[GSYM WORD_LEFT_AND_OVER_OR, WORD_OR_COMP, WORD_AND_CLAUSES] >>
  `(x && m) && x = x && m` by
    metis_tac[WORD_AND_ASSOC, WORD_AND_COMM, WORD_AND_IDEM] >>
  `word_and (word_and x m) (word_and x (word_1comp m)) = 0w` by
    metis_tac[WORD_AND_ASSOC, WORD_AND_COMP, WORD_AND_CLAUSES] >>
  metis_tac[WORD_ADD_OR, WORD_ADD_SUB, WORD_ADD_COMM]
QED

Theorem abi_bytes_low_five:
  ∀x:bytes32. x && 31w = n2w (w2n x MOD 32)
Proof
  gen_tac >>
  `x = n2w (w2n x)` by simp[] >>
  pop_assum SUBST1_TAC >>
  `31w:bytes32 = n2w (2 ** 5 - 1)` by EVAL_TAC >>
  pop_assum SUBST1_TAC >>
  PURE_REWRITE_TAC [WORD_AND_EXP_SUB1] >>
  simp[wordsTheory.w2n_n2w, wordsTheory.w2n_lt]
QED

Theorem abi_bytes_sub_mod_32[local]:
  ∀n. n - n MOD 32 = 32 * (n DIV 32)
Proof
  gen_tac >>
  mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >>
  simp[] >> disch_then (qspec_then `n` mp_tac) >> decide_tac
QED

Theorem abi_bytes_mask_shift:
  ∀x:bytes32.
    x && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w =
    word_lsl (word_lsr x 5) 5
Proof
  gen_tac >>
  `x && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w =
     n2w (w2n x - w2n x MOD 32)` by
    (`x = n2w (w2n x)` by simp[] >>
     `w2n x MOD 32 ≤ w2n x` by
       simp[arithmeticTheory.MOD_LESS_EQ] >>
     ONCE_REWRITE_TAC [abi_bytes_mask_not_31] >>
     ONCE_REWRITE_TAC [abi_bytes_and_complement] >>
     ONCE_REWRITE_TAC [abi_bytes_low_five] >>
     metis_tac[wordsTheory.n2w_sub]) >>
  `word_lsl (word_lsr x 5) 5 = n2w (32 * (w2n x DIV 32))` by
    (`word_lsr x 5 = n2w (w2n (word_lsr x 5))` by simp[] >>
     pop_assum SUBST1_TAC >>
     simp[wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr]) >>
  simp[abi_bytes_sub_mod_32]
QED

Theorem abi_bytes_ceil32_div[local]:
  ∀n. venomLayout$ceil32 n = ((n + 31) DIV 32) * 32
Proof
  gen_tac >>
  mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >>
  simp[] >> disch_then (qspec_then `n` strip_assume_tac) >>
  Cases_on `n MOD 32 = 0`
  >- (`n + 31 = n DIV 32 * 32 + 31` by decide_tac >>
      PURE_REWRITE_TAC [venomLayoutTheory.ceil32_def] >>
      simp[arithmeticTheory.DIV_MULT] >> decide_tac) >>
  `0 < n MOD 32` by decide_tac >>
  `n + 31 = (n DIV 32 + 1) * 32 + (n MOD 32 - 1)` by decide_tac >>
  `n MOD 32 < 32` by
    (irule arithmeticTheory.MOD_LESS >> simp[]) >>
  `n MOD 32 - 1 < 32` by decide_tac >>
  `(n + 31) DIV 32 = n DIV 32 + 1` by
    (once_rewrite_tac
       [ASSUME ``n + 31 = (n DIV 32 + 1) * 32 + (n MOD 32 - 1)``] >>
     irule arithmeticTheory.DIV_MULT >> simp[]) >>
  rw[venomLayoutTheory.ceil32_def] >> decide_tac
QED

Theorem abi_bytes_round_word:
  ∀n. n ≤ dimword (:256) - 32 ⇒
    word_and ((n2w n : bytes32) + 31w)
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w =
    n2w (venomLayout$ceil32 n)
Proof
  rpt strip_tac >>
  `n + 31 < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  simp[abi_bytes_mask_shift, wordsTheory.word_add_n2w,
       wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr,
       arithmeticTheory.LESS_MOD, abi_bytes_ceil32_div,
       arithmeticTheory.MULT_COMM] >>
  `word_lsr (n2w (n + 31) : bytes32) 5 =
     n2w (w2n (word_lsr (n2w (n + 31) : bytes32) 5))` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
       arithmeticTheory.MULT_COMM]
QED


Theorem abi_bytes_ceil32_gap:
  ∀n. n ≤ venomLayout$ceil32 n ∧ venomLayout$ceil32 n ≤ n + 32
Proof
  gen_tac >> simp[venomLayoutTheory.ceil32_ge, venomLayoutTheory.ceil32_def] >>
  `n MOD 32 < 32` by simp[] >> decide_tac
QED

Theorem abi_bytes_ceil32_eq:
  ∀n. venomLayout$ceil32 n = contractABI$ceil32 n
Proof
  simp[abi_bytes_ceil32_div, contractABITheory.ceil32_def,
       arithmeticTheory.MULT_COMM]
QED


Theorem abi_bytes_round_mask_first:
  ∀n. n ≤ dimword (:256) - 32 ⇒
    word_and
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
      (31w + (n2w n:bytes32)) =
    n2w (venomLayout$ceil32 n)
Proof
  rpt strip_tac >>
  `word_and
     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w
     (31w + (n2w n:bytes32)) =
   word_and ((n2w n:bytes32) + 31w)
     0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w` by
    metis_tac[wordsTheory.WORD_AND_COMM, wordsTheory.WORD_ADD_COMM] >>
  metis_tac[abi_bytes_round_word]
QED

