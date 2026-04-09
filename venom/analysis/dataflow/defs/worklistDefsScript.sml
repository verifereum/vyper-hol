(*
 * Worklist Iteration — Definitions
 *
 * Worklist-based fixpoint iteration matching the Python compiler's
 * deque-based worklist (FIFO: pop front, push back).
 *
 * process : 'a -> 'b -> 'b    (process one label, return new state)
 * changed : 'a -> 'b -> 'b -> bool  (detect whether deps need re-adding)
 * deps    : 'a -> 'a list     (labels to re-add when a label changes)
 *
 * The changed predicate examines the label, old state, and new state
 * to decide whether to add deps. This avoids comparing full states
 * (which may contain structures like fmaps that lack decidable equality
 * under EVAL). For dataflow analyses, changed compares one boundary value.
 *
 * The convergence theorems (in proofs/) take an invariant P so that
 * inflationary need only hold under P.  For the unconditional case,
 * instantiate P = λ_. T.
 *
 * TOP-LEVEL:
 *   wl_step           — single worklist step
 *   wl_iterate        — iterate to fixpoint via WHILE
 *   wl_deps_complete  — deps cover all affected labels
 *   is_fixpoint       — no label changes state
 *)

Theory worklistDefs
Ancestors
  latticeDefs While

(* Single worklist step: pop front, process, push deps if changed *)
Definition wl_step_def:
  wl_step changed process deps p =
    case FST p of
      [] => p
    | lbl :: rest =>
        let st' = process lbl (SND p) in
        if changed lbl (SND p) st' then (rest ++ deps lbl, st')
        else (rest, st')
End

(* Iterate to fixpoint *)
Definition wl_iterate_def:
  wl_iterate changed process deps wl0 st0 =
    WHILE (\p. FST p <> [])
          (wl_step changed process deps)
          (wl0, st0)
End

(* Deps are complete: after processing lbl reports a change, every label
   that would report a change on the new state (and was either lbl itself
   or was at fixpoint for the old state) is in deps(lbl). *)
Definition wl_deps_complete_def:
  wl_deps_complete changed (process : 'a -> 'b -> 'b) (deps : 'a -> 'a list) <=>
    !lbl (st : 'b).
      changed lbl st (process lbl st) ==>
      !b. changed b (process lbl st) (process b (process lbl st)) /\
          (b = lbl \/ ~changed b st (process b st)) ==>
          MEM b (deps lbl)
End

(* Fixpoint predicate: processing any label is a no-op *)
Definition is_fixpoint_def:
  is_fixpoint (process : 'a -> 'b -> 'b) all_lbls st <=>
    !lbl. MEM lbl all_lbls ==> process lbl st = st
End
