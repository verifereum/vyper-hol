(*
 * Power-of-two bridge lemma: is_power_of_two w ==> w2n w = 2^k.
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

(* Variant with ≤ and ≠ *)
val bit_h_pred_le = prove(
  ``!h n. 2 ** h <= n ==> n <> 2 ** h ==> n < 2 ** SUC h ==>
          BIT h (n - 1)``,
  rpt strip_tac >> irule bit_h_pred >> decide_tac);

(* LOG2_PROPERTY rewritten to use bit.LOG2 *)
val LOG2_PROPERTY' =
  REWRITE_RULE [GSYM bitTheory.LOG2_def] logrootTheory.LOG2_PROPERTY;

(* word_bit in terms of BIT on w2n *)
val WORD_BIT_W2N = prove(
  ``!n (w:'a word). word_bit n w <=> n < dimindex(:'a) /\ BIT n (w2n w)``,
  rpt gen_tac >>
  `w = n2w (w2n w)` by simp[wordsTheory.n2w_w2n] >>
  pop_assum SUBST1_TAC >>
  simp[wordsTheory.word_bit_n2w, wordsTheory.w2n_n2w, wordsTheory.w2n_lt] >>
  EQ_TAC >> strip_tac >> simp[] >>
  `1 <= dimindex(:'a)` by simp[fcpTheory.DIMINDEX_GE_1] >> simp[]);

(* Main theorem proved at SML level to avoid overloading issues *)
val is_power_of_two_exp = save_thm("is_power_of_two_exp",
  prove(
    ``!w : bytes32. is_power_of_two w ==>
      ?k. w2n w = 2 ** k /\ k < dimindex(:256)``,
    rw[is_power_of_two_def] >> rpt strip_tac >>
    qexists_tac `LOG2 (w2n w)` >>
    conj_tac >| [
      (* First conjunct: w2n w = 2 ** LOG2 (w2n w) *)
      `(w2n w:num) <> 0` by simp[wordsTheory.w2n_eq_0] >>
      CCONTR_TAC >>
      `0 < w2n w` by simp[] >>
      first_assum (mp_tac o MATCH_MP LOG2_PROPERTY') >>
      strip_tac >>
      (let
        val w2n_w = ``w2n (w:bytes32)``
        val log2_w2n = mk_comb(prim_mk_const{Thy="bit", Name="LOG2"}, w2n_w)
      in
        first_assum (fn le =>
          first_assum (fn neq =>
            first_assum (fn lt =>
              assume_tac (MP (MP (MP
                (SPECL [log2_w2n, w2n_w] bit_h_pred_le)
                le) neq) lt))))
      end) >>
      imp_res_tac bitTheory.BIT_LOG2 >>
      imp_res_tac wordsTheory.LOG2_w2n_lt >>
      `1w <=+ (w:bytes32)` by
        simp[wordsTheory.WORD_LS, wordsTheory.w2n_n2w] >>
      imp_res_tac wordsTheory.word_sub_w2n >>
      `word_bit (LOG2 (w2n w)) w` by simp[WORD_BIT_W2N] >>
      `word_bit (LOG2 (w2n w)) (w - 1w)` by
        simp[WORD_BIT_W2N, wordsTheory.w2n_n2w] >>
      `word_bit (LOG2 (w2n w)) (w && (w - 1w))` by
        simp[wordsTheory.word_bit_and] >>
      gvs[wordsTheory.word_bit_0],
      (* Second conjunct: LOG2 (w2n w) < 256 *)
      imp_res_tac wordsTheory.LOG2_w2n_lt >> fs[]
    ]));

val _ = export_theory();
