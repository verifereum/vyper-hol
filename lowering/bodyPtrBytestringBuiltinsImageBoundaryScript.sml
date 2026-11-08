(* Exact bounded list summaries retain full records, including operand names.
   These algebraic facts do not certify any supported compiler producer. *)
Theory bodyPtrBytestringBuiltinsImageBoundary
Ancestors bodyPtrBytestringBuiltinsWindows list rich_list arithmetic

Theorem bounded_prefix_append:
  !n xs ys.
    TAKE n (TAKE n xs ++ TAKE n ys) = TAKE n (xs ++ ys)
Proof
  rpt gen_tac >> Cases_on `n <= LENGTH xs`
  >- simp[rich_listTheory.TAKE_APPEND, LENGTH_TAKE_EQ, TAKE_TAKE_MIN, MIN_DEF] >>
  `LENGTH xs <= n` by decide_tac >>
  simp[rich_listTheory.TAKE_APPEND, LENGTH_TAKE_EQ, TAKE_TAKE_MIN, MIN_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem bounded_suffix_append:
  !n xs ys.
    REVERSE (TAKE n (REVERSE
      (REVERSE (TAKE n (REVERSE xs)) ++
       REVERSE (TAKE n (REVERSE ys))))) =
    REVERSE (TAKE n (REVERSE (xs ++ ys)))
Proof
  simp[REVERSE_APPEND, bounded_prefix_append]
QED

Theorem bounded_prefix_associative:
  !n xs ys zs.
    TAKE n (TAKE n (xs ++ ys) ++ TAKE n zs) =
    TAKE n (TAKE n xs ++ TAKE n (ys ++ zs))
Proof
  simp[bounded_prefix_append, APPEND_ASSOC]
QED
