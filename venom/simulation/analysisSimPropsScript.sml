(*
 * Analysis-Driven Simulation — Correctness (Statements Only)
 *
 * Re-exports some results from proofs/ via ACCEPT_TAC; the rest live only
 * in the proofs/ theories, so import those for them.
 *
 * TOP-LEVEL:
 *   analysis_inst_sim_block_sim         — per-inst sim → per-block sim
 *   analysis_inst_sim_block_sim_inv     — per-block sim with state_inv
 *   df_analysis_pass_correct_sound_inv3  — inv3 variant (transfer_sound_block_inv)
 *   analysis_inst_simulates_from_1       — 1:1 special case of inst_simulates
 *   transfer_sound_exit_wf_len          — transfer_sound_exit_wf + bb_well_formed
 *   fwd_df_at_entry_eq_joined           — entry df_at equals joined value at fixpoint
 *   fwd_df_at_exit_not_none             — exit df_at non-NONE when entry non-NONE
 *   fwd_joined_sound_from_pred          — joined value sound from one pred
 *   fwd_df_at_entry_not_none            — entry df_at non-bottom at fixpoint
 *)

Theory analysisSimProps
Ancestors
  analysisSimProofs analysisSimProofsBase analysisSimProofsSound
  analysisSimProofsFwd

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
         run_block fuel run_ctx bb s = OK v ==>
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
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (!bb s s_phi.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         eval_phis s bb.bb_instructions = OK s_phi /\
         sound (df_at bottom result bb.bb_label 0) s /\
         state_inv s ==>
         sound (df_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0) /\
         state_inv (s_phi with vs_inst_idx := 0))
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

(* Like transfer_sound_exit_wf but derives EVERY inst_wf from bb_well_formed
   (which implies inst_wf for all instructions in the block). *)
Theorem transfer_sound_exit_wf_len =
  analysisSimProofsTheory.transfer_sound_exit_wf_len

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
  ACCEPT_TAC analysisSimProofsFwdTheory.fwd_df_at_entry_eq_joined
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
  ACCEPT_TAC analysisSimProofsFwdTheory.fwd_df_at_exit_not_none
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
  ACCEPT_TAC analysisSimProofsFwdTheory.fwd_joined_sound_from_pred
QED

(* At a forward fixpoint, if the entry value is non-bottom and the function
   entry label matches, then df_at is non-bottom at index 0 for every
   label in DFS pre-order. *)
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
  ACCEPT_TAC analysisSimProofsFwdTheory.fwd_df_at_entry_not_none
QED
