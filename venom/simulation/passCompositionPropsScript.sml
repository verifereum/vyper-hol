(*
 * Analysis-Driven Pass Composition — Correctness (Statement Only)
 *
 * Re-exports from proofs/passCompositionProofsScript.sml via ACCEPT_TAC.
 *)

Theory passCompositionProps
Ancestors
  passCompositionProofs passSimulationProps

Theorem analysis_pass_correct:
  !(R : venom_state -> venom_state -> bool)
   (leq : 'a -> 'a -> bool) m b
   (process : 'c -> 'a -> 'a)
   (deps : 'c -> 'c list)
   (wl0 : 'c list) (st0 : 'a)
   (all_lbls : 'c list)
   (P : 'a -> bool)
   (sound : 'a -> bool)
   (transform : 'a -> basic_block -> basic_block).
    (!lbl st. P st ==> leq st (process lbl st)) /\
    (!lbl st. P st ==> P (process lbl st)) /\
    P st0 /\
    bounded_measure P leq m b /\
    wl_deps_complete process deps /\
    (!lbl. MEM lbl all_lbls ==> MEM lbl wl0) /\
    (!st. is_fixpoint process all_lbls st ==> sound st) /\
    (!analysis. sound analysis ==>
       block_simulates R (transform analysis)) /\
    (!analysis bb. (transform analysis bb).bb_label = bb.bb_label)
  ==>
    let analysis = SND (wl_iterate process deps wl0 st0) in
    !fuel fn s.
      lift_result R (run_function fuel fn s)
                 (run_function fuel
                   (function_map_transform (transform analysis) fn) s)
Proof
  ACCEPT_TAC analysis_pass_correct_proof
QED
