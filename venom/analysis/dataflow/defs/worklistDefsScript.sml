(*
 * Worklist Iteration — Definitions
 *
 * Worklist-based fixpoint iteration matching the Python compiler's
 * deque-based worklist (FIFO: pop front, push back).
 *
 * process : 'a -> 'b -> 'b    (process one label, return new state)
 * deps    : 'a -> 'a list     (labels to re-add when a label changes)
 * Changed is detected by st' <> st (no explicit flag).
 *
 * TOP-LEVEL:
 *   wl_step           — single worklist step
 *   wl_iterate        — iterate to fixpoint via WHILE
 *   wl_inflationary   — process only grows state
 *   wl_deps_complete  — deps cover all affected labels
 *   is_fixpoint       — no label changes state
 *)

Theory worklistDefs
Ancestors
  latticeDefs While

(* Single worklist step: pop front, process, push deps if changed *)
Definition wl_step_def:
  wl_step process deps p =
    case FST p of
      [] => p
    | lbl :: rest =>
        let st' = process lbl (SND p) in
        if st' <> SND p then (rest ++ deps lbl, st')
        else (rest, SND p)
End

(* Iterate to fixpoint *)
Definition wl_iterate_def:
  wl_iterate process deps wl0 st0 =
    WHILE (\p. FST p <> [])
          (wl_step process deps)
          (wl0, st0)
End

(* Process is inflationary: state can only grow *)
Definition wl_inflationary_def:
  wl_inflationary (leq : 'b -> 'b -> bool)
                  (process : 'a -> 'b -> 'b) <=>
    !lbl st. leq st (process lbl st)
End

(* Deps are complete: after processing lbl changes st, every label
   that newly needs processing (including lbl itself if applicable)
   is in deps(lbl).
   Specifically: if b wants to change the new state, and either
   b = lbl (self-affecting) or b was at fixpoint for the old state,
   then b must be in deps(lbl). *)
Definition wl_deps_complete_def:
  wl_deps_complete (process : 'a -> 'b -> 'b) (deps : 'a -> 'a list) <=>
    !lbl (st : 'b).
      process lbl st <> st ==>
      !b. process b (process lbl st) <> process lbl st /\
          (b = lbl \/ process b st = st) ==>
          MEM b (deps lbl)
End

(* Fixpoint predicate: processing any label is a no-op *)
Definition is_fixpoint_def:
  is_fixpoint (process : 'a -> 'b -> 'b) all_lbls st <=>
    !lbl. MEM lbl all_lbls ==> process lbl st = st
End
