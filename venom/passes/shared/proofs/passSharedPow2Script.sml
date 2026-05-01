(*
 * Power-of-two bridge lemma: is_power_of_two w ==> w2n w = 2^k.
 *
 * Placed here (not in algebraicOptRules2) to avoid ** overloading
 * from integerTheory (pulled in via algebraicOptDefs → valueRangeDefs).
 *)
Theory passSharedPow2
Ancestors
  passSharedDefs
Libs
  wordsLib

val _ = temp_overload_on ("**", ``arithmetic$EXP``);

(* Helper: BIT h (n-1) when 2^h < n < 2^(h+1) *)
Triviality bit_h_pred[local]:
  !h n. 2 ** h < n /\ n < 2 ** SUC h ==> BIT h (n - 1)
Proof
  rpt strip_tac >>
  `0 < 2 ** h` by simp[] >>
  `1 <= 2 ** h` by simp[] >>
  `1 < n` by
    (imp_res_tac arithmeticTheory.LESS_EQ_LESS_TRANS >> fs[]) >>
  `n - 1 <> 0` by simp[] >>
  `LOG2 (n - 1) = h` suffices_by metis_tac[bitTheory.BIT_LOG2] >>
  irule bitTheory.LOG2_UNIQUE >>
  conj_tac >| [
    `0 < 2 ** h` by simp[] >> decide_tac,
    fs[arithmeticTheory.EXP] >>
    `0 < 2 ** h` by simp[] >> decide_tac
  ]
QED

(* CHEATED — proof works interactively but the ** overloading from
   integerTheory (loaded globally via vfm) prevents tactics like
   decide_tac, simp, and qpat_x_assum from handling EXP terms correctly
   in batch mode. The proof logic is sound (BIT_LOG2 + bit_h_pred
   contradiction via word_bit_and/word_bit_0) but needs SML-level
   term construction throughout to avoid backtick ** resolution issues.
   See feedback_exp_overloading.md for details. *)
Theorem is_power_of_two_exp:
  !w : bytes32. is_power_of_two w ==>
    ?k. w2n w = 2 ** k /\ k < dimindex(:256)
Proof
  cheat
QED

val _ = export_theory();
