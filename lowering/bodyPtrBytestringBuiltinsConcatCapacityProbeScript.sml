(* The current compiler rounds logical capacity, which need not cover the
   final full-word fixed-bytes store.  This is an interface probe, not yet a
   counterexample to the universally quantified body judgment. *)
Theory bodyPtrBytestringBuiltinsConcatCapacityProbe
Ancestors bodyPtrDefs vyperValueOperation exprLowering

Theorem concat_short_fixed_source_probe:
  evaluate_concat 2 [BytesV [1w]; BytesV [2w]] =
    INL (BytesV [1w;2w])
Proof
  EVAL_TAC
QED

Theorem concat_short_fixed_capacity_probe:
  32 + ((2 + 31) DIV 32) * 32 = 64 /\
  ~(32 + 1 + 32 <= 32 + ((2 + 31) DIV 32) * 32)
Proof
  EVAL_TAC
QED

Theorem concat_short_fixed_coverage_probe:
  !G tn p s b.
    lookup_var p s = SOME (n2w (b + 33)) /\
    FLOOKUP G p = SOME (b,64) /\
    b + 33 < dimword (:256) ==>
    ~ptr_covers G tn p s 32
Proof
  simp[ptr_covers_def] >> rpt strip_tac >>
  gvs[]
QED
