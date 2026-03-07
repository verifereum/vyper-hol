(*
 * Analysis-Driven Simulation — Proofs
 *
 * TOP-LEVEL:
 *   analysis_inst_sim_block_sim_proof    — per-inst sim → block sim (universal sound)
 *   df_analysis_pass_correct_proof       — end-to-end: analysis + transform → function sim
 *)

Theory analysisSimProofs
Ancestors
  analysisSimDefs dfAnalyzeProofs passSimulationDefs

(* When sound = λv s. T (analysis doesn't constrain states),
   analysis_inst_simulates implies block simulation unconditionally.
   This is the common case for liveness-driven dead code elimination. *)
Theorem analysis_inst_sim_block_sim_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f : 'a -> instruction -> instruction).
    analysis_inst_simulates R_ok R_term (λv s. T) f
  ==>
    block_simulates R_ok R_term (analysis_block_transform bottom result f)
Proof
  cheat
QED

(* End-to-end pass correctness using df_analyze.
   Combines: convergence + universal-sound transform → function-level lift_result.

   For state-dependent soundness (e.g., range analysis), a separate theorem
   with transfer_sound + initial_sound preconditions is needed — see design
   notes in TASK_df_refactor.md. *)
Theorem df_analysis_pass_correct_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (f : 'a -> instruction -> instruction)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      (* Worklist convergence preconditions *)
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      (* Transform simulation (universal soundness) *)
      analysis_inst_simulates R_ok R_term (λ(v:'a) s. T) f /\
      (* R_ok preserves control flow *)
      (!s1 s2. R_ok s1 s2 ==> s1.vs_current_bb = s2.vs_current_bb) /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted)
    ==>
      !fuel s.
        lift_result R_ok R_term (run_function fuel fn s)
          (run_function fuel (analysis_function_transform bottom result f fn) s)
Proof
  cheat
QED
