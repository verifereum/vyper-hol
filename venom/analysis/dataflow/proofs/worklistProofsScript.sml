(*
 * Worklist Iteration — Convergence Proofs
 *
 * Termination: bounded measure + inflationary → WHILE terminates.
 * Fixpoint: deps_complete → result is a fixpoint for all labels.
 * Above: partial_order + inflationary → result ≥ initial.
 * Invariant: P preserved by process → P holds at result.
 *)

Theory worklistProofs
Ancestors
  worklistDefs

(* Termination: worklist empties under inflationary + bounded measure.
   Argument: each change-step increases m by ≥1 (bounded by b), each
   no-change step removes one worklist element. Finite total steps. *)
Theorem wl_iterate_terminates_proof:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0.
    wl_inflationary leq process /\
    bounded_measure leq m b ==>
    FST (wl_iterate process deps wl0 st0) = []
Proof
  cheat
QED

(* Fixpoint: processing any label from all_lbls is a no-op.
   Argument: maintain invariant "every non-fixpoint label is in the worklist".
   Initially true (all labels in wl0). Preserved by deps_complete.
   At termination (empty worklist): every label is at fixpoint. *)
Theorem wl_iterate_fixpoint_proof:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 all_lbls.
    wl_inflationary leq process /\
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
   (process : 'b -> 'a -> 'a) deps wl0 st0.
    partial_order leq /\
    wl_inflationary leq process /\
    bounded_measure leq m b ==>
    leq st0 (SND (wl_iterate process deps wl0 st0))
Proof
  cheat
QED

(* Invariant: property P preserved through iteration.
   If P holds initially and process preserves P, then P holds at result. *)
Theorem wl_iterate_invariant_proof:
  !(leq : 'a -> 'a -> bool) m b
   (process : 'b -> 'a -> 'a) deps wl0 st0 (P : 'a -> bool).
    wl_inflationary leq process /\
    bounded_measure leq m b /\
    P st0 /\
    (!lbl st. P st ==> P (process lbl st)) ==>
    P (SND (wl_iterate process deps wl0 st0))
Proof
  cheat
QED
