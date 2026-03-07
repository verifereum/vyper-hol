(*
 * Analysis-Driven Simulation — Correctness (Statements Only)
 *
 * Re-exports from proofs/analysisSimProofsScript.sml via ACCEPT_TAC.
 *)

Theory analysisSimProps
Ancestors
  analysisSimProofs

(* Transform preserves block labels. *)
Theorem analysis_block_transform_label:
  !(bottom : 'a) (result : 'a df_state) f bb.
    (analysis_block_transform bottom result f bb).bb_label = bb.bb_label
Proof
  ACCEPT_TAC analysis_block_transform_label_proof
QED

(* Universal-sound analysis_inst_simulates implies block_simulates.
   Covers liveness-based dead code elimination and similar passes
   where the transform is safe regardless of concrete state. *)
Theorem analysis_inst_sim_block_sim:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f : 'a -> instruction -> instruction).
    analysis_inst_simulates R_ok R_term (λv s. T) f
  ==>
    block_simulates R_ok R_term (analysis_block_transform bottom result f)
Proof
  ACCEPT_TAC analysis_inst_sim_block_sim_proof
QED

(* End-to-end: df_analyze convergence + universal-sound transform →
   function-level lift_result. *)
Theorem df_analysis_pass_correct:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join transfer edge_transfer ctx fn
   (f : 'a -> instruction -> instruction)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let wl0 = (case dir of
                 Forward => cfg.cfg_dfs_pre
               | Backward => cfg.cfg_dfs_post) in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
    let result = df_analyze dir bottom join transfer edge_transfer ctx fn in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      P st0 /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      (!lbl. MEM lbl all_lbls ==> MEM lbl wl0) /\
      analysis_inst_simulates R_ok R_term (λ(v:'a) s. T) f /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_current_bb = s2.vs_current_bb) /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted)
    ==>
      !fuel s.
        lift_result R_ok R_term (run_function fuel fn s)
          (run_function fuel (analysis_function_transform bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_proof
QED
