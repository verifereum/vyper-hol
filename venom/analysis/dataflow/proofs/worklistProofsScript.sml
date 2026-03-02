(*
 * Worklist Iteration — Convergence Proofs
 *
 * All theorems take an invariant P so that inflationary need only
 * hold under P.  For the unconditional case, instantiate P = λ_. T.
 *
 * Termination: bounded measure + inflationary-under-P → WHILE terminates.
 * Fixpoint: deps_complete → result is a fixpoint for all labels.
 * Above: partial_order + inflationary-under-P → result ≥ initial.
 * Invariant: P preserved by process → P holds at result.
 *)

Theory worklistProofs
Ancestors
  worklistDefs

(* Termination: worklist empties under inflationary-under-P + bounded measure.
   Argument: P is an invariant, so inflationary holds at every intermediate
   state.  Each change-step increases m by ≥1 (bounded by b), each
   no-change step removes one worklist element.  Finite total steps. *)
Theorem wl_iterate_terminates_proof:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure leq m b ==>
    FST (wl_iterate process deps wl0 st0) = []
Proof
  cheat
QED

(* Fixpoint: processing any label from all_lbls is a no-op.
   Argument: maintain invariant "every non-fixpoint label is in the worklist".
   Initially true (all labels in wl0).  Preserved by deps_complete.
   At termination (empty worklist): every label is at fixpoint. *)
Theorem wl_iterate_fixpoint_proof:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 all_lbls (P : 'a -> bool).
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure leq m b /\
    wl_deps_complete process deps /\
    (!lbl. MEM lbl all_lbls ==> MEM lbl wl0) ==>
    is_fixpoint process all_lbls (SND (wl_iterate process deps wl0 st0))
Proof
  cheat
QED

(* Above: result state is above initial state.
   Needs partial_order for transitivity to chain through iteration. *)
Theorem wl_iterate_above_proof:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    partial_order leq /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure leq m b ==>
    leq st0 (SND (wl_iterate process deps wl0 st0))
Proof
  cheat
QED

(* Invariant: property P preserved through iteration.
   If P holds initially and process preserves P, then P holds at result.
   Also needs inflationary-under-P for termination (WHILE may not
   terminate otherwise, making the result undefined). *)
Theorem wl_iterate_invariant_proof:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure leq m b ==>
    P (SND (wl_iterate process deps wl0 st0))
Proof
  cheat
QED
