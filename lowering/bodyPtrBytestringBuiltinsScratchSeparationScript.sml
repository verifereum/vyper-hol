Theory bodyPtrBytestringBuiltinsScratchSeparation
Ancestors bodyPtrBytestringBuiltinsConcatFrame compileEnv pred_set

(* n is the physical payload write width: 32 for the fixed arm. *)
Theorem scratch_two_windows_separated:
  (!name lb len. local_region cenv scopes s name lb len ==>
    a+cap <= lb \/ lb+len <= a) /\
  (!name lb len. local_region cenv scopes s name lb len ==>
    b+sz <= lb \/ lb+len <= b) /\
  k+n <= cap /\ 32 <= sz ==>
  !name lb len i. local_region cenv scopes s name lb len /\
    lb <= i /\ i < lb+len ==>
    i NOTIN ({j | a+k <= j /\ j < a+k+n} UNION {j | b <= j /\ j < b+32})
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `a+cap <= lb \/ lb+len <= a` by metis_tac[] >>
  `b+sz <= lb \/ lb+len <= b` by metis_tac[] >>
  simp[] >> decide_tac
QED
