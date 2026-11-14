(* The word copy loop's index arithmetic: word i of an n-word buffer at b
   below the frontier ends below it too. *)
Theory bodyMemAssignTopCopyIndex
Ancestors
  venomState words arithmetic

Theorem topcopy_index_bound:
  w2n b + 32*n <= s.vs_alloca_next /\ i < n ==>
  w2n (b + n2w i * 32w : 256 word) + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  `b + n2w i * 32w = n2w (w2n b + 32*i)` by
    simp[GSYM word_add_n2w, GSYM word_mul_n2w, arithmeticTheory.MULT_COMM,
         WORD_MULT_COMM] >>
  asm_rewrite_tac[] >>
  `w2n (n2w (w2n b + 32*i) : 256 word) <= w2n b + 32*i` by
    simp[w2n_n2w, arithmeticTheory.MOD_LESS_EQ] >>
  decide_tac
QED
