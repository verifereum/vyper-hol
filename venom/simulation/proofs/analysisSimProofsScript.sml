(*
 * Analysis-Driven Simulation — Proofs
 *
 * 1:N is the primary framework. 1:1 is derived via inst_simulates_implies_1n.
 *
 * TOP-LEVEL:
 *   analysis_inst_sim_block_sim_1n_proof         — block-level lifting
 *   df_analysis_pass_correct_1n_proof             — end-to-end (universal sound)
 *   df_analysis_pass_correct_1n_sound_proof       — end-to-end (state-dependent)
 *   df_analysis_pass_correct_1n_widen_sound_proof — end-to-end (widening)
 *   inst_simulates_implies_1n_proof               — 1:1 is special case of 1:N
 *)

Theory analysisSimProofs
Ancestors
  analysisSimDefs dfAnalyzeProofs dfAnalyzeWidenProofs passSimulationDefs

(* When sound = λv s. T, analysis_inst_simulates_1n implies block simulation.
   Proof sketch: induction on original block. For each original instruction,
   the expansion is processed by run_block as non-terminator non-INVOKE
   steps (matching run_insts modulo inst_idx). Terminators and INVOKE
   pass through unchanged. *)
Theorem analysis_inst_sim_block_sim_1n_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f : 'a -> instruction -> instruction list).
    analysis_inst_simulates_1n R_ok R_term (\v s. T) f
  ==>
    block_simulates R_ok R_term (analysis_block_transform_1n bottom result f)
Proof
  cheat
QED

(* Universal-sound 1:N pass correctness (non-widening). *)
Theorem df_analysis_pass_correct_1n_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (f : 'a -> instruction -> instruction list)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      analysis_inst_simulates_1n R_ok R_term (\(v:'a) s. T) f /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_current_bb = s2.vs_current_bb) /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted)
    ==>
      !fuel ctx s.
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_1n bottom result f fn) s)
Proof
  cheat
QED

(* State-dependent 1:N pass correctness (non-widening). *)
Theorem df_analysis_pass_correct_1n_sound_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      transfer_sound sound transfer ctx /\
      edge_transfer_sound sound edge_transfer ctx /\
      (!a b s. sound a s ==> sound (join a b) s) /\
      (!s. sound bottom s) /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => !s. sound v s) /\
      analysis_inst_simulates_1n R_ok R_term sound f /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_current_bb = s2.vs_current_bb) /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted)
    ==>
      !fuel ctx s.
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_1n bottom result f fn) s)
Proof
  cheat
QED

(* State-dependent 1:N pass correctness (widening). *)
Theorem df_analysis_pass_correct_1n_widen_sound_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list)
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      transfer_sound sound transfer ctx /\
      edge_transfer_sound sound edge_transfer ctx /\
      (!a b s. sound a s ==> sound (join a b) s) /\
      (!a b s. sound a s ==> sound (widen a b) s) /\
      (!s. sound bottom s) /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => !s. sound v s) /\
      analysis_inst_simulates_1n R_ok R_term sound f /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_current_bb = s2.vs_current_bb) /\
      (!s1 s2. R_ok s1 s2 ==> s1.vs_halted = s2.vs_halted)
    ==>
      !fuel ctx s.
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_1n_widen bottom result f fn) s)
Proof
  cheat
QED

(* 1:1 is a special case of 1:N with singleton output.
   run_insts [g v inst] s = step_inst (g v inst) s (when step gives OK or terminal).
   FLAT (MAPi (λi inst. [g v_i inst]) insts) = MAPi (λi inst. g v_i inst) insts. *)
Theorem inst_simulates_implies_1n_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (g : 'a -> instruction -> instruction).
    analysis_inst_simulates R_ok R_term sound g ==>
    analysis_inst_simulates_1n R_ok R_term sound (\v inst. [g v inst])
Proof
  cheat
QED
