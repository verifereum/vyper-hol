(*
 * Analysis-Driven Simulation — Correctness (Statements Only)
 *
 * Re-exports from proofs/analysisSimProofsScript.sml via ACCEPT_TAC.
 * 1:1 corollary: analysis_inst_simulates_from_1.
 *)

Theory analysisSimProps
Ancestors
  analysisSimProofs analysisSimProofsBase

(* Per-instruction sim → per-block sim.
   Requires valid_state_rel, R_ok/R_term transitivity,
   sound simulation, and operand agreement under R_ok. *)
Theorem analysis_inst_sim_block_sim:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f : 'a -> instruction -> instruction list) bb.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!i s. i < LENGTH bb.bb_instructions ==>
           sound (df_at bottom result bb.bb_label i) s)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
          (analysis_block_transform bottom result f bb) s)
Proof
  ACCEPT_TAC analysis_inst_sim_block_sim_proof
QED

(* Block sim with state_inv threaded to per-inst sim.
   Wraps analysis_block_sim_inv from ProofsBase, adding fn_inst_wf -> EVERY. *)
Theorem analysis_inst_sim_block_sim_inv:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (bottom : 'a) (result : 'a df_state) transfer run_ctx
   (f : 'a -> instruction -> instruction list) bb.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!fuel ctx v inst s.
       sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result R_ok R_term R_term (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    inst_transform_structural f /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (!fuel ctx inst s s'.
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      state_inv s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  qspecl_then [`R_ok`, `R_term`, `sound`, `state_inv`, `f`, `bb`,
    `bottom`, `result`, `transfer`, `run_ctx`]
    mp_tac analysis_block_sim_inv >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (qpat_x_assum `transfer_sound _ _ _` mp_tac >>
         rw[analysisSimDefsTheory.transfer_sound_def,
            analysisSimDefsTheory.transfer_sound_wf_def]) >>
    simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
    fs[venomWfTheory.fn_inst_wf_def] >> res_tac) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

(* End-to-end dataflow pass correctness (state-dependent soundness).
   Requires convergence witnesses to establish fixpoint of df_analyze. *)
Theorem df_analysis_pass_correct_sound:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx (analysis_function_transform bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_sound_proof
QED

(* Non-widen variant with state_inv + transfer_sound_wf.
   For predicates that need an auxiliary state invariant (e.g. dfg_assigns_sound)
   that's preserved by well-formed step_inst but not by arbitrary ones.
   Per-inst sim gets both sound AND state_inv; conclusion requires state_inv. *)
Theorem df_analysis_pass_correct_sound_inv2:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound_wf sound transfer ctx /\
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      (!fuel ctx' v inst s.
         sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
         (?e. step_inst fuel ctx' inst s = Error e) \/
         lift_result R_ok R_term R_term (step_inst fuel ctx' inst s)
           (run_insts fuel ctx' (f v inst) s)) /\
      inst_transform_structural f /\
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!fuel ctx' bb inst s s'.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         inst_wf inst /\
         state_inv (s with vs_inst_idx := 0) /\
         step_inst fuel ctx' inst s = OK s' ==>
         state_inv (s' with vs_inst_idx := 0)) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx' s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s ==>
        (?e. run_blocks fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx' fn s)
          (run_blocks fuel ctx' (analysis_function_transform bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_sound_inv2_proof
QED

(* Block-restricted transfer soundness variant.
   Like inv2 but transfer_sound_block_inv replaces transfer_sound_wf:
   soundness only needs to hold for instructions from fn's blocks,
   and the transfer proof can use state_inv. *)
Theorem df_analysis_pass_correct_sound_inv3:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound_block_inv sound state_inv transfer ctx fn /\
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      (!fuel ctx' v inst s.
         sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
         (?e. step_inst fuel ctx' inst s = Error e) \/
         lift_result R_ok R_term R_term (step_inst fuel ctx' inst s)
           (run_insts fuel ctx' (f v inst) s)) /\
      inst_transform_structural f /\
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!fuel ctx' bb inst s s'.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         inst_wf inst /\
         state_inv (s with vs_inst_idx := 0) /\
         step_inst fuel ctx' inst s = OK s' ==>
         state_inv (s' with vs_inst_idx := 0)) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx' s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s ==>
        (?e. run_blocks fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx' fn s)
          (run_blocks fuel ctx' (analysis_function_transform bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_sound_inv3_proof
QED

(* Widening variant. Uses entry/successor soundness with df_widen_at. *)
Theorem df_analysis_pass_correct_widen_sound:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen Forward bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze_widen Forward bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (* Entry soundness *)
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_widen_at bottom result lbl 0) s) /\
      (* Successor soundness *)
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_widen_sound_proof
QED

(* Widening variant with additional state invariant.
   Threads state_inv through induction; only requires state_inv for
   the initial state (in conclusion), not universally. *)
Theorem df_analysis_pass_correct_widen_sound_inv:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen Forward bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze_widen Forward bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        sound (df_widen_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_widen_sound_inv_proof
QED

(* Variant with transfer_sound_wf and state_inv threaded to per-inst sim.
   For predicates like dfg_ext_sound that are preserved through well-formed
   instructions but not arbitrary ones. *)
Theorem df_analysis_pass_correct_widen_sound_inv2:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen Forward bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze_widen Forward bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound_wf sound transfer ctx /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      (!fuel ctx' v inst s.
         sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
         (?e. step_inst fuel ctx' inst s = Error e) \/
         lift_result R_ok R_term R_term (step_inst fuel ctx' inst s)
           (run_insts fuel ctx' (f v inst) s)) /\
      inst_transform_structural f /\
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!fuel ctx' bb inst s s'.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         inst_wf inst /\
         state_inv (s with vs_inst_idx := 0) /\
         step_inst fuel ctx' inst s = OK s' ==>
         state_inv (s' with vs_inst_idx := 0)) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx' s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        sound (df_widen_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx' fn s)
          (run_blocks fuel ctx'
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_widen_sound_inv2_proof
QED

(* 1:1 is a special case with singleton output. *)
Theorem analysis_inst_simulates_from_1:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (g : 'a -> instruction -> instruction).
    analysis_inst_simulates_1 R_ok R_term sound g ==>
    analysis_inst_simulates R_ok R_term sound (\v inst. [g v inst])
Proof
  ACCEPT_TAC analysis_inst_simulates_from_1_proof
QED

(* Prepend-aware pass correctness. *)
Theorem df_analysis_pass_correct_prepend:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list)
   (prepend : string -> instruction list).
    let cfg = cfg_analyze fn in
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    let fn' = analysis_function_transform_prepend
                bottom result prepend f fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint (df_process_block Forward bottom join transfer edge_transfer
                     ctx entry_val cfg fn.fn_blocks) cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (* Prepend succeeds and preserves R_ok *)
      (!lbl fuel ctx s.
         s.vs_inst_idx = 0 ==>
         ?s'. run_insts fuel ctx (prepend lbl) s = OK s' /\ R_ok s s') /\
      (* Prepend instructions are non-terminator, non-INVOKE *)
      (!lbl inst. MEM inst (prepend lbl) ==>
         ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE) /\
      (* Operand agreement for full transformed function *)
      (!bb inst x.
         MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx fn' s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_prepend_proof
QED

(* Compare two analysis_function_transforms of the same function.
   Useful when a pass decomposes into substitution + elimination phases
   that use different transform functions on the same analysis result. *)
Theorem analysis_function_transform_compare:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f1 : 'a -> instruction -> instruction list)
   (f2 : 'a -> instruction -> instruction list) fn.
    let fn1 = analysis_function_transform bottom result f1 fn in
    let fn2 = analysis_function_transform bottom result f2 fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb idx fuel ctx s.
       MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions ==>
       let inst = EL idx bb.bb_instructions in
       let v = df_at bottom result bb.bb_label idx in
       (?e. run_insts fuel ctx (f1 v inst) s = Error e) \/
       lift_result R_ok R_term R_term
         (run_insts fuel ctx (f1 v inst) s)
         (run_insts fuel ctx (f2 v inst) s)) /\
    inst_transform_structural f1 /\
    inst_transform_structural f2 /\
    fn_inst_wf fn /\
    (!bb inst x.
       MEM bb fn1.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_blocks fuel ctx fn1 s = Error e) \/
      lift_result R_ok R_term R_term
        (run_blocks fuel ctx fn1 s)
        (run_blocks fuel ctx fn2 s)
Proof
  ACCEPT_TAC analysis_function_transform_compare_proof
QED

(* DFS pre-order is closed under successors *)
Theorem cfg_dfs_pre_succs_closed:
  !fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    EVERY (\t. MEM t (cfg_analyze fn).cfg_dfs_pre)
          (cfg_succs_of (cfg_analyze fn) lbl)
Proof
  ACCEPT_TAC cfg_dfs_pre_succs_closed
QED

(* Transfer-sound single step: sound at idx + step_inst OK → sound at SUC idx *)
Theorem transfer_sound_step:
  !sound transfer run_ctx inst fuel ctx s s' v_in v_out.
    transfer_sound sound transfer run_ctx /\
    sound v_in s /\
    step_inst fuel ctx inst s = OK s' /\
    v_out = transfer run_ctx inst v_in ==>
    sound v_out s'
Proof
  ACCEPT_TAC transfer_sound_step
QED

(* Transfer-sound chain: running original block from sound entry gives
   sound exit value at SUC terminator-index. *)
Theorem transfer_sound_exit:
  !R_ok R_term sound transfer run_ctx bb bottom result.
    valid_state_rel R_ok R_term /\
    transfer_sound sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s v i.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      exec_block fuel ctx bb s = OK v /\
      i < LENGTH bb.bb_instructions /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
      sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  ACCEPT_TAC transfer_sound_exit
QED

(* Like transfer_sound_exit but uses transfer_sound_wf + EVERY inst_wf.
   Useful when the soundness predicate needs inst_wf (e.g. FDOM coverage). *)
Theorem transfer_sound_exit_wf:
  !R_ok R_term sound transfer run_ctx bb bottom result.
    valid_state_rel R_ok R_term /\
    transfer_sound_wf sound transfer run_ctx /\
    EVERY inst_wf bb.bb_instructions /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s v i.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      exec_block fuel ctx bb s = OK v /\
      i < LENGTH bb.bb_instructions /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
      sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  ACCEPT_TAC analysisSimProofsTheory.transfer_sound_exit_wf
QED

(* Like transfer_sound_exit_wf but uses bb_well_formed to give LENGTH *)
Theorem transfer_sound_exit_wf_len =
  analysisSimProofsTheory.transfer_sound_exit_wf_len

(* After running a block OK, the successor block is in cfg_dfs_pre *)
Theorem successor_in_cfg_dfs_pre:
  !fn bb fuel ctx s v.
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    exec_block fuel ctx bb s = OK v
    ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  ACCEPT_TAC analysisSimProofsTheory.successor_in_cfg_dfs_pre
QED

(* At fixpoint (Forward), df_at bottom result lbl 0 = joined value *)
Theorem fwd_df_at_entry_eq_joined:
  !(bottom : 'a) join transfer edge_transfer ctx entry_val fn lbl.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    wf_function fn /\
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer ctx
         entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    df_at bottom result lbl 0 =
    df_joined_val Forward bottom join edge_transfer ctx entry_val
      (cfg_analyze fn) result lbl
Proof
  ACCEPT_TAC analysisSimProofsTheory.fwd_df_at_entry_eq_joined
QED

(* Forward df_at at exit index is non-NONE when entry is non-NONE *)
Theorem fwd_df_at_exit_not_none:
  !(bottom : 'a option) join transfer edge_transfer (ctx : 'b)
   entry_val fn lbl bb.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer ctx
         entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> [] /\
    (!inst v. v <> NONE ==> transfer ctx inst v <> NONE) /\
    df_at bottom result lbl 0 <> NONE ==>
    df_at bottom result lbl (LENGTH bb.bb_instructions) <> NONE
Proof
  ACCEPT_TAC analysisSimProofsTheory.fwd_df_at_exit_not_none
QED

(* General: if one predecessor's boundary is sound and non-NONE,
   then df_joined_val is sound. Shared by all forward analyses. *)
Theorem fwd_joined_sound_from_pred:
  !(join : 'a option -> 'a option -> 'a option)
   (edge_transfer : 'b -> string -> string -> 'a option -> 'a option)
   (ctx : 'b) (entry_val : (string # 'a option) option) cfg
   (result : 'a option df_state)
   (sound : 'a option -> 'd -> bool) fn lbl nbr v.
    (!a b s. sound a s /\ a <> NONE ==> sound (join a b) s) /\
    (!a b s. sound b s /\ b <> NONE ==> sound (join a b) s) /\
    (!a b. a <> NONE \/ b <> NONE ==> join a b <> NONE) /\
    (!ev_lbl ev a s. entry_val = SOME (ev_lbl, ev) ==>
                     sound a s ==> sound (join ev a) s) /\
    MEM nbr (cfg_preds_of cfg lbl) /\
    edge_transfer ctx nbr lbl (df_boundary NONE result nbr) <> NONE /\
    sound (edge_transfer ctx nbr lbl (df_boundary NONE result nbr)) v
    ==>
    sound (df_joined_val Forward NONE join edge_transfer ctx entry_val
             cfg result lbl) v
Proof
  ACCEPT_TAC analysisSimProofsTheory.fwd_joined_sound_from_pred
QED

(* General forward successor entry soundness — shared by all forward passes *)
Theorem fwd_successor_entry_sound:
  !(bottom : 'a option) join transfer edge_transfer
   (ctx : 'b) entry_val fn
   (sound : 'a option -> venom_state -> bool)
   (R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   bb (fuel : num) run_ctx s v.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    let cfg = cfg_analyze fn in
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer ctx
         entry_val cfg fn.fn_blocks) cfg.cfg_dfs_pre result /\
    wf_function fn /\ fn_inst_wf fn /\
    ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    MEM s.vs_current_bb cfg.cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    sound (df_at bottom result s.vs_current_bb 0) s /\
    exec_block fuel run_ctx bb s = OK v /\
    (* H1: transfer_sound *)
    transfer_sound sound transfer ctx /\
    (* H2: valid_state_rel + sound respects R_ok *)
    valid_state_rel R_ok R_term /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (* H3: transfer preserves SOME *)
    (!inst v. v <> NONE ==> transfer ctx inst v <> NONE) /\
    (* H4: join-right soundness *)
    (!a b s. sound b s /\ b <> NONE ==> sound (join a b) s) /\
    (* H5: edge_transfer preserves soundness *)
    (!src dst val s. sound val s ==> sound (edge_transfer ctx src dst val) s) /\
    (* H6: edge_transfer preserves SOME *)
    (!src dst val. val <> NONE ==> edge_transfer ctx src dst val <> NONE) /\
    (* H7: joined sound from one pred *)
    (!lbl nbr.
       MEM nbr (cfg_preds_of cfg lbl) /\
       edge_transfer ctx nbr lbl (df_boundary bottom result nbr) <> NONE /\
       sound (edge_transfer ctx nbr lbl (df_boundary bottom result nbr)) v
       ==>
       sound (df_joined_val Forward bottom join edge_transfer ctx entry_val
                cfg result lbl) v) /\
    (* H8: entry value at current block is non-bottom *)
    df_at bottom result s.vs_current_bb 0 <> NONE /\
    (* H9: join preserves non-bottom *)
    (!a b. b <> NONE ==> join a b <> NONE)
    ==>
    MEM v.vs_current_bb cfg.cfg_dfs_pre /\
    sound (df_at bottom result v.vs_current_bb 0) v
Proof
  ACCEPT_TAC analysisSimProofsTheory.fwd_successor_entry_sound
QED

Theorem fwd_df_at_entry_not_none:
  !(bottom : 'a) join transfer edge_transfer ctx entry_val fn lbl.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    (!ctx' inst v. transfer ctx' inst v <> bottom) /\
    (!a b. a <> bottom \/ b <> bottom ==> join a b <> bottom) /\
    (!ctx' src dst v. v <> bottom ==> edge_transfer ctx' src dst v <> bottom) /\
    (?ev_lbl ev. entry_val = SOME (ev_lbl, ev) /\
       fn_entry_label fn = SOME ev_lbl /\
       ev <> bottom)
    ==>
    df_at bottom result lbl 0 <> bottom
Proof
  ACCEPT_TAC analysisSimProofsTheory.fwd_df_at_entry_not_none
QED
