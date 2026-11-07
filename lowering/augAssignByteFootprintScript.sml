(* Pointwise transfer only: consumers must prove exposure coverage from
   descriptor-compatible writes. The source and IR footprints may differ. *)
Theory augAssignByteFootprint
Ancestors
  vyperStorage list

Theorem saved_bytes_footprint_transfer:
  (!k b. live k b ==>
    EL b (word_to_bytes (lookup_storage k src) T) =
    EL b (word_to_bytes (lookup_storage k ir) T)) /\
  (!k b. ~wsrc k ==>
    EL b (word_to_bytes (lookup_storage k src') T) =
    EL b (word_to_bytes (lookup_storage k src) T)) /\
  (!k b. ~wir k ==>
    EL b (word_to_bytes (lookup_storage k ir') T) =
    EL b (word_to_bytes (lookup_storage k ir) T)) /\
  (!k b. live' k b ==>
    (live k b /\ ~wsrc k /\ ~wir k) \/
    EL b (word_to_bytes (lookup_storage k src') T) =
    EL b (word_to_bytes (lookup_storage k ir') T)) ==>
  !k b. live' k b ==>
    EL b (word_to_bytes (lookup_storage k src') T) =
    EL b (word_to_bytes (lookup_storage k ir') T)
Proof
  metis_tac[]
QED

Theorem saved_bytes_touched_transfer:
  (!k b. live k b ==>
    EL b (word_to_bytes (lookup_storage k src) T) =
    EL b (word_to_bytes (lookup_storage k ir) T)) /\
  (!k b. ~wsrc k ==>
    EL b (word_to_bytes (lookup_storage k src') T) =
    EL b (word_to_bytes (lookup_storage k src) T)) /\
  (!k b. ~wir k ==>
    EL b (word_to_bytes (lookup_storage k ir') T) =
    EL b (word_to_bytes (lookup_storage k ir) T)) /\
  (!k b. live' k b /\ (wsrc k \/ wir k) ==>
    EL b (word_to_bytes (lookup_storage k src') T) =
    EL b (word_to_bytes (lookup_storage k ir') T)) /\
  (!k b. live' k b /\ ~wsrc k /\ ~wir k ==> live k b) ==>
  !k b. live' k b ==>
    EL b (word_to_bytes (lookup_storage k src') T) =
    EL b (word_to_bytes (lookup_storage k ir') T)
Proof
  metis_tac[saved_bytes_footprint_transfer]
QED
