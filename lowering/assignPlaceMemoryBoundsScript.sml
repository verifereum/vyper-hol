Theory assignPlaceMemoryBounds
Ancestors
  placeDestinationBounds words

(* Diagnostic only: even a word-aligned region with a positive address
   does not yield the size-plus-64 premise from its strict end bound. *)
Theorem assign_place_destination_room_probe[local]:
  let base = 32; size = dimword (:256) - 64 in
    0 < base /\ 0 < size /\ size MOD 32 = 0 /\
    base + size < dimword (:256) /\
    ~(size + 64 < dimword (:256))
Proof
  simp[wordsTheory.dimword_def] >> EVAL_TAC
QED
