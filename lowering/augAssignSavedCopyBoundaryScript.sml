(* Symbolic coverage obligations, not nested encoding equalities. *)
Theory augAssignSavedCopyBoundary
Ancestors
  augAssignCopyFootprint stmtSimStoreCopy venomState vyperStorage words list

Theorem normalized_copy_saved_inside_iff:
  store_copy_normalize s t =
    store_copy_prefix (if tr then LocTransient else LocStorage) buf k s n /\
  w2n k+n <= dimword (:256) ==>
  ((!q b. live q b /\ w2n k <= w2n q /\ w2n q < w2n k+n ==>
    EL b (word_to_bytes (lookup_storage q post) T) =
    EL b (word_to_bytes (if tr then tload q t else sload q t) T)) <=>
   (!q b. live q b /\ w2n k <= w2n q /\ w2n q < w2n k+n ==>
    EL b (word_to_bytes (lookup_storage q post) T) =
    EL b (word_to_bytes
      (mload (w2n (buf+n2w (w2n q-w2n k)*32w)) s) T)))
Proof
  strip_tac >> drule_all normalized_copy_prefix_footprint >>
  strip_tac >> eq_tac >> rpt strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem normalized_copy_saved_outside_iff:
  store_copy_normalize s t =
    store_copy_prefix (if tr then LocTransient else LocStorage) buf k s n /\
  w2n k+n <= dimword (:256) ==>
  ((!q b. live q b /\ ~(w2n k <= w2n q /\ w2n q < w2n k+n) ==>
    EL b (word_to_bytes (lookup_storage q post) T) =
    EL b (word_to_bytes (if tr then tload q t else sload q t) T)) <=>
   (!q b. live q b /\ ~(w2n k <= w2n q /\ w2n q < w2n k+n) ==>
    EL b (word_to_bytes (lookup_storage q post) T) =
    EL b (word_to_bytes (if tr then tload q s else sload q s) T)))
Proof
  strip_tac >> drule_all normalized_copy_prefix_footprint >>
  strip_tac >> eq_tac >> rpt strip_tac >>
  first_x_assum drule_all >> simp[]
QED
