(*
 * Worklist Iteration — Correctness (Statements Only)
 *
 * Convergence and fixpoint theorems for worklist-based iteration.
 * All take an invariant P (instantiate with λ_. T for unconditional).
 * Proofs live in proofs/worklistProofsScript.sml;
 * this file re-exports via ACCEPT_TAC.
 *)

Theory worklistProps
Ancestors
  worklistProofs

(* Worklist empties under inflationary-under-P + bounded measure. *)
Theorem wl_iterate_terminates:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure leq m b ==>
    FST (wl_iterate process deps wl0 st0) = []
Proof
  ACCEPT_TAC wl_iterate_terminates_proof
QED

(* Processing any label is a no-op at termination. *)
Theorem wl_iterate_fixpoint:
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
  ACCEPT_TAC wl_iterate_fixpoint_proof
QED

(* Result state is above initial state. *)
Theorem wl_iterate_above:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    partial_order leq /\
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure leq m b ==>
    leq st0 (SND (wl_iterate process deps wl0 st0))
Proof
  ACCEPT_TAC wl_iterate_above_proof
QED

(* Property P preserved through iteration. *)
Theorem wl_iterate_invariant:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure leq m b ==>
    P (SND (wl_iterate process deps wl0 st0))
Proof
  ACCEPT_TAC wl_iterate_invariant_proof
QED
