(* Array evaluation positivity is typed_memory_array_stride_bounds in
   placeMemoryTypedBase; reuse that boundary rather than duplicating it. *)
Theory bodyPtrPopLocalRootBounds
Ancestors exprSimPop placeMemoryTypedBase arithmetic words

Theorem pop_local_interior_bounds:
  0 < esz /\ 0 < len /\ len <= cap /\
  32 + cap * esz <= bytes ==>
  32 < bytes /\ 32 + (len-1)*esz < bytes /\
  32 + (len-1)*esz + esz <= bytes
Proof
  strip_tac >>
  `32 + (len-1)*esz + esz <= bytes` by
    (mp_tac (Q.SPECL [`len`, `cap`, `esz`, `esz`, `bytes`, `0`] pop_elem_fits) >>
     simp[]) >>
  `0 <= (len-1)*esz` by simp[] >> decide_tac
QED

Theorem pop_local_interior_word_bound:
  w2n (a:bytes32) + bytes <= dimword(:256) /\ off < bytes ==>
  w2n a + off < dimword(:256)
Proof
  decide_tac
QED
