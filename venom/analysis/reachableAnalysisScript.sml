(*
 * Reachable Analysis
 *
 * Port of venom/analysis/reachable.py.
 *)

Theory reachableAnalysis
Ancestors
  list finite_map
  orderedSet
  venomInst
  cfgAnalysis

Datatype:
  reachable_analysis = <|
    reachable : (string, string list) fmap
  |>
End

Definition reachable_compute_def:
  reachable_compute cfg_out lbl reach fuel =
    case fuel of
      0 => reach
    | SUC fuel' =>
        (case FLOOKUP reach lbl of
           SOME _ => reach
         | NONE =>
             let succs = fmap_lookup_ordset cfg_out lbl in
             let reach0 = reach |+ (lbl, succs) in
             let reach1 =
               FOLDL (λm s. reachable_compute cfg_out s m fuel') reach0 succs in
             let s =
               FOLDL
                 (λacc s. ordset_union acc (fmap_lookup_ordset reach1 s))
                 succs succs in
             reach1 |+ (lbl, s))
End

Definition reachable_analyze_def:
  reachable_analyze fn cfg =
    case entry_block fn of
      NONE => <| reachable := FEMPTY |>
    | SOME bb =>
        let fuel = LENGTH fn.fn_blocks + 1 in
        let reach = reachable_compute cfg.cfg_out bb.bb_label FEMPTY fuel in
        <| reachable := reach |>
End

val _ = export_theory();
