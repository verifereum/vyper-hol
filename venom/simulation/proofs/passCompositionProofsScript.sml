(*
 * Analysis-Driven Pass Composition — Proofs
 *
 * TOP-LEVEL:
 *   analysis_pass_correct_proof — worklist convergence + block sim ⟹ function sim
 *)

Theory passCompositionProofs
Ancestors
  passSimulationDefs execEquivParamDefs
  latticeDefs worklistDefs dfIterateDefs

Theorem analysis_pass_correct_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
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
       block_simulates R_ok R_term (transform analysis)) /\
    (!analysis bb. (transform analysis bb).bb_label = bb.bb_label) /\
    (!s1 s2. R_ok s1 s2 ==> s1.vs_current_bb = s2.vs_current_bb) /\
    (!s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted)
  ==>
    let analysis = SND (wl_iterate process deps wl0 st0) in
    !fuel fn s.
      lift_result R_ok R_term (run_function fuel fn s)
                 (run_function fuel
                   (function_map_transform (transform analysis) fn) s)
Proof
  cheat
QED
