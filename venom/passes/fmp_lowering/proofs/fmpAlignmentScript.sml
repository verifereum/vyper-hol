(* Modular alignment boundary for the DALLOCA expansion. *)
Theory fmpAlignment
Ancestors
  venomLayout words
Libs
  wordsLib

Theorem dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem ceil32_div_mul:
  !n. ceil32 n = ((n + 31) DIV 32) * 32
Proof
  gen_tac >>
  mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >>
  simp[] >> disch_then (qspec_then `n` strip_assume_tac) >>
  Cases_on `n MOD 32 = 0`
  >- (`n + 31 = n DIV 32 * 32 + 31` by decide_tac >>
      simp[ceil32_def, arithmeticTheory.DIV_MULT]) >>
  `0 < n MOD 32` by decide_tac >>
  `n + 31 = (n DIV 32 + 1) * 32 + (n MOD 32 - 1)` by decide_tac >>
  `n MOD 32 < 32` by (irule arithmeticTheory.MOD_LESS >> simp[]) >>
  `n MOD 32 - 1 < 32` by decide_tac >>
  `(n + 31) DIV 32 = n DIV 32 + 1` by
    (qpat_x_assum `n + 31 = _` (fn th => once_rewrite_tac [th]) >>
     irule arithmeticTheory.DIV_MULT >> simp[]) >>
  rw[ceil32_def] >> decide_tac
QED

Theorem word_clear_low5[local]:
  !w:256 word. w && ~31w = (w >>> 5) << 5
Proof
  gen_tac >> rewrite_tac[GSYM WORD_EQ] >>
  simp_tac bool_ss [word_bit_def, dimindex_256] >> rpt strip_tac >>
  pure_rewrite_tac [word_and_def, word_1comp_def, word_lsl_def, word_lsr_def] >>
  asm_simp_tac (std_ss ++ fcpLib.FCP_ss) [dimindex_256, n2w_def] >>
  `x - 5 < 256` by decide_tac >>
  qspecl_then [`x`, `5`] mp_tac bitTheory.BIT_EXP_SUB1 >>
  simp[] >> Cases_on `x < 5` >>
  asm_simp_tac (arith_ss ++ fcpLib.FCP_ss) [dimindex_256]
QED

Theorem dalloca_mask_value:
  !sz:256 word. (sz + 31w) && ~31w = n2w (ceil32 (w2n sz))
Proof
  gen_tac >> rewrite_tac[word_clear_low5] >>
  qmatch_goalsub_abbrev_tac `q << 5` >>
  `q = n2w (w2n q)` by simp[] >> pop_assum SUBST1_TAC >>
  simp[word_lsl_n2w, w2n_lsr, word_add_def, Abbr `q`, ceil32_div_mul] >>
  qspecl_then [`w2n sz + 31`, `32`, `2 ** 251`] mp_tac arithmeticTheory.DIV_MOD_MOD_DIV >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  simp[arithmeticTheory.MOD_COMMON_FACTOR]
QED

Theorem dalloca_mask_aligned:
  !sz:256 word. w2n ((sz + 31w) && ~31w) MOD 32 = 0
Proof
  gen_tac >> rewrite_tac[dalloca_mask_value, w2n_n2w, ceil32_div_mul] >>
  qspecl_then [`2 ** 251`, `32`] mp_tac arithmeticTheory.MOD_MULT_MOD >>
  simp[] >>
  disch_then (qspec_then `32 * ((w2n sz + 31) DIV 32)` mp_tac) >>
  simp[dimword_def]
QED

(* Boundary probes include the wraparound at the largest word. *)
Theorem dalloca_mask_examples[local]:
  (((0w:256 word) + 31w) && ~31w = 0w) /\
  (((1w:256 word) + 31w) && ~31w = 32w) /\
  (((31w:256 word) + 31w) && ~31w = 32w) /\
  (((32w:256 word) + 31w) && ~31w = 32w) /\
  (((-1w:256 word) + 31w) && ~31w = 0w)
Proof
  EVAL_TAC
QED

val _ = List.app (fn (name, th) =>
  if null (Thm.hyp th) andalso
     List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("Incomplete alignment theorem: " ^ name))
  (DB.thms "fmpAlignment");
