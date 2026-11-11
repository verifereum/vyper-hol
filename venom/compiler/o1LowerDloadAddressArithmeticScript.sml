Theory o1LowerDloadAddressArithmetic
Ancestors words venomState

Theorem lower_dload_translate_endpoint:
  !x b c sz.
    b <= w2n (x:bytes32) /\ w2n x <= b+sz /\
    b+sz < dimword (:256) /\ c+sz < dimword (:256) ==>
    w2n (x + n2w c - n2w b) = c + (w2n x - b)
Proof
  rpt strip_tac >>
  `w2n x = b + (w2n x - b)` by decide_tac >>
  `x = n2w b + n2w (w2n x - b)` by
    (pure_rewrite_tac[wordsTheory.word_add_n2w] >>
     qpat_x_assum `w2n x = _` (SUBST1_TAC o GSYM) >>
     pure_rewrite_tac[wordsTheory.n2w_w2n] >> REFL_TAC) >>
  qpat_x_assum `w2n x = _` kall_tac >>
  `x + n2w c - n2w b = n2w (c + (w2n x - b))` by
    (pure_rewrite_tac[GSYM wordsTheory.word_add_n2w] >>
     qpat_x_assum `x = _`
       (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     qabbrev_tac `p = (n2w b:bytes32)` >>
     qabbrev_tac `q = (n2w (w2n x - b):bytes32)` >>
     qabbrev_tac `r = (n2w c:bytes32)` >>
     POP_ASSUM_LIST (K ALL_TAC) >> wordsLib.WORD_DECIDE_TAC) >>
  `c + (w2n x - b) < dimword (:256)` by decide_tac >>
  qpat_x_assum `x + _ - _ = _`
    (fn th => pure_rewrite_tac[th, wordsTheory.w2n_n2w]) >>
  irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC
QED

Theorem lower_dload_translate_add:
  !x z b c. ((x:bytes32) + n2w c - n2w b) + z =
             (x + z) + n2w c - n2w b
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem lower_dload_translate_sub:
  !x z b c. ((x:bytes32) + n2w c - n2w b) - z =
             (x - z) + n2w c - n2w b
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem lower_dload_translate_comparisons:
  !x y b c sz.
    b <= w2n (x:bytes32) /\ w2n x <= b+sz /\
    b <= w2n (y:bytes32) /\ w2n y <= b+sz /\
    b+sz < dimword (:256) /\ c+sz < dimword (:256) ==>
    ((x = y) <=> (x + n2w c - n2w b = y + n2w c - n2w b)) /\
    ((w2n x < w2n y) <=>
      (w2n (x + n2w c - n2w b) < w2n (y + n2w c - n2w b))) /\
    ((w2n y < w2n x) <=>
      (w2n (y + n2w c - n2w b) < w2n (x + n2w c - n2w b)))
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (x + n2w c - n2w b) = c + (w2n x - b)` by
    (irule lower_dload_translate_endpoint >> asm_rewrite_tac[] >>
     qexists_tac `sz` >> asm_rewrite_tac[]) >>
  `w2n (y + n2w c - n2w b) = c + (w2n y - b)` by
    (irule lower_dload_translate_endpoint >> asm_rewrite_tac[] >>
     qexists_tac `sz` >> asm_rewrite_tac[]) >>
  pure_rewrite_tac[GSYM wordsTheory.w2n_11] >>
  asm_rewrite_tac[] >> decide_tac
QED
