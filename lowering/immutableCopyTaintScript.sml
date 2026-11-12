(* Constructor copies can overlap: each load reads the evolving memory taint.
   This small set recurrence mirrors the sequential word stores; it is not
   another execution judgment. *)
Theory immutableCopyTaint
Ancestors ptrDiscipline abiDecodeStaticProps words arithmetic pred_set

Definition immutable_copy_taints_def:
  immutable_copy_taints ctor (a:bytes32) (b:bytes32) 0 off M = M /\
  immutable_copy_taints ctor a b (SUC n) off M =
    immutable_copy_taints ctor a b n (off+32)
      ((M DIFF {i | w2n (b+n2w off) <= i /\ i < w2n (b+n2w off)+32}) UNION
       IMAGE (\j. w2n (b+n2w off)+j)
         (if ctor then mem_word_taint M (w2n (a+n2w off)) else {}))
End

Theorem immutable_copy_taints_zero[simp]:
  immutable_copy_taints ctor a b 0 off M = M
Proof
  simp[immutable_copy_taints_def]
QED

Theorem immutable_copy_taints_one:
  immutable_copy_taints ctor a b 1 off M =
    (M DIFF {i | w2n (b+n2w off) <= i /\ i < w2n (b+n2w off)+32}) UNION
    IMAGE (\j. w2n (b+n2w off)+j)
      (if ctor then mem_word_taint M (w2n (a+n2w off)) else {})
Proof
  pure_rewrite_tac[ONE, immutable_copy_taints_def] >> REFL_TAC
QED

Theorem mem_word_taint_bound:
  j IN mem_word_taint M at ==> j < 32
Proof
  simp[mem_word_taint_def]
QED

Theorem immutable_copy_taints_untouched:
  !n off M i.
    w2n b + off + 32*n <= dimword(:256) /\
    (i < w2n b + off \/ w2n b + off + 32*n <= i) ==>
    (i IN immutable_copy_taints ctor a b n off M <=> i IN M)
Proof
  Induct_on `n` >- simp[] >> rpt gen_tac >> strip_tac >>
  `w2n b + off < dimword(:256)` by decide_tac >>
  `w2n (b+n2w off) = w2n b + off` by simp[w2n_add_n2w_lt] >>
  `w2n b + (off+32) + 32*n <= dimword(:256) /\
   (i < w2n b + (off+32) \/ w2n b + (off+32) + 32*n <= i)` by
    decide_tac >>
  simp[Once immutable_copy_taints_def] >>
  Cases_on `ctor` >> simp[mem_word_taint_def] >>
  simp[EQ_IMP_THM] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem immutable_copy_taints_word_frame:
  w2n b + off + 32*n <= dimword(:256) /\
  (addr + 32 <= w2n b + off \/ w2n b + off + 32*n <= addr) ==>
  mem_word_taint (immutable_copy_taints ctor a b n off M) addr =
    mem_word_taint M addr
Proof
  strip_tac >> simp[EXTENSION, mem_word_taint_def] >> gen_tac >>
  Cases_on `x < 32` >> simp[] >>
  irule immutable_copy_taints_untouched >> simp[] >> decide_tac
QED

Theorem immutable_copy_taints_head_clean:
  0 < n /\ w2n b + 32*n <= dimword(:256) /\
  (ctor ==> mem_word_taint M (w2n a) = {}) ==>
  mem_word_taint (immutable_copy_taints ctor a b n 0 M) (w2n b) = {}
Proof
  Cases_on `n` >- simp[] >> strip_tac >>
  `mem_word_taint M (w2n a) = {} \/ ~ctor` by metis_tac[] >>
  `w2n b < dimword(:256)` by decide_tac >>
  simp[Once immutable_copy_taints_def, WORD_ADD_0] >>
  `w2n b + 32 + 32*n' <= dimword(:256)` by decide_tac >>
  `!M'. mem_word_taint (immutable_copy_taints ctor a b n' 32 M') (w2n b) =
        mem_word_taint M' (w2n b)` by
    (gen_tac >> irule immutable_copy_taints_word_frame >> simp[]) >>
  simp[] >> Cases_on `ctor` >>
  gvs[EXTENSION, mem_word_taint_def] >> decide_tac
QED
