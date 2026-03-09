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
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeWidenProofs
  passSimulationDefs

(* ===== Block-level lifting ===== *)

(* Per-instruction 1:N simulation → per-block simulation.
   Needs valid_state_rel + transitivity for triangle composition,
   plus operand condition: R_ok-related states agree on all operand
   variables of bb's instructions.
   For INVOKE/terminators: analysis_inst_simulates_1n requires
   f v inst = [inst], so both sides dispatch identically. *)
Theorem analysis_inst_sim_block_sim_1n_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f : 'a -> instruction -> instruction list) bb.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates_1n R_ok R_term (\v s. T) f /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      lift_result R_ok R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx
          (analysis_block_transform_1n bottom result f bb) s)
Proof
  cheat
QED

(* ===== End-to-end pass correctness ===== *)

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
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      analysis_inst_simulates_1n R_ok R_term (\(v:'a) s. T) f /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
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
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
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
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
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
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
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
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_1n_widen bottom result f fn) s)
Proof
  cheat
QED

(* ===== 1:1 as special case ===== *)

(* 1:1 is a special case of 1:N with singleton output.
   run_insts fuel ctx [g v inst] s reduces to step_inst fuel ctx (g v inst) s.
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
