Theory bodyPtrIfExpMemoryVariation
Ancestors
  valueEncodingProps allocationPtr typedCopyPtr

(* Duplicating a source window correlates the destinations. Arbitrarily
   perturbing both tainted destinations independently need not be realizable
   by perturbing the initial source. This is not an IfExp counterexample. *)
Theorem ifexp_duplicated_copy_windows:
  !s src d1 d2 n.
    (src + n <= d1 \/ d1 + n <= src) /\
    (d1 + n <= d2 \/ d2 + n <= d1) ==>
    mem_bytes_at d1 n (mcopy d2 src n (mcopy d1 src n s)).vs_memory =
    mem_bytes_at d2 n (mcopy d2 src n (mcopy d1 src n s)).vs_memory
Proof
  rpt strip_tac >>
  simp[mcopy_mem_bytes_at_disjoint, mcopy_mem_bytes_at_same]
QED

(* Even one byte need not be freely realizable after a taint-permitted
   non-byte-aligned shift: zero-fill constrains some bits of that byte. *)
Theorem ifexp_shift_low_byte_not_arbitrary:
  !w : bytes32. ((7 >< 0) (w << 1) : word8) <> 1w
Proof
  wordsLib.WORD_DECIDE_TAC
QED
