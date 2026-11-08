(* Rounded copy capacity uses semantic layout, never an identification of
   the source compiler layout with an independently laid-out destination. *)
Theory bodyPtrMakeArrayLayout
Ancestors
  valueEncodingProps arithmetic

(* The alignment equation itself is body_immutable_copy_aligned_size.
   Do not re-export it or import its unrelated memory-proof dependencies;
   the slot-size identity suffices for these distinct capacity bounds. *)
Theorem semantic_copy_word_bounds:
  m = type_memory_size tv ==>
  (!i. i <= (m + 31) DIV 32 ==> 32 * i <= m) /\
  (!i. i < (m + 31) DIV 32 ==> 32 * i + 32 <= m)
Proof
  strip_tac >>
  `32 * ((m + 31) DIV 32) = m` by
    simp[type_memory_size_slots, MULT_DIV] >>
  conj_tac >> rpt strip_tac >> decide_tac
QED
