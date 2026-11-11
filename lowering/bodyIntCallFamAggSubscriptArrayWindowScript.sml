(* A selected fixed-array element stays in its parent's authorized window. *)
Theory bodyIntCallFamAggSubscriptArrayWindow
Ancestors
  words arithmetic exprSimProps

Theorem intcall_array_element_window:
  a <= w2n (b:256 word) /\
  w2n b + n * sz <= a + k /\ a + k < dimword (:256) /\ j < n ==>
  w2n (b + n2w (j * sz)) = w2n b + j * sz /\
  a <= w2n (b + n2w (j * sz)) /\
  w2n (b + n2w (j * sz)) + sz <= a + k
Proof
  strip_tac >>
  `SUC j <= n` by decide_tac >>
  `j * sz + sz <= n * sz` by
    metis_tac[MULT_CLAUSES, ADD_COMM, LESS_MONO_MULT] >>
  `w2n b + n * sz < dimword (:256)` by decide_tac >>
  `j * sz <= n * sz` by decide_tac >>
  drule_all buffer_offset_no_wrap >> strip_tac >> simp[]
QED
