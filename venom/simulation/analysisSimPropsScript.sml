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
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx
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
       lift_result R_ok R_term (step_inst fuel ctx inst s)
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
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx
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
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
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
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx (analysis_function_transform bottom result f fn) s)
Proof
  ACCEPT_TAC df_analysis_pass_correct_sound_proof
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
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
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
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
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
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      analysis_inst_simulates R_ok R_term sound f /\
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
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
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
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      (!fuel ctx' v inst s.
         sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
         (?e. step_inst fuel ctx' inst s = Error e) \/
         lift_result R_ok R_term (step_inst fuel ctx' inst s)
           (run_insts fuel ctx' (f v inst) s)) /\
      inst_transform_structural f /\
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
        (?e. run_function fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx' fn s)
          (run_function fuel ctx'
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
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
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
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx fn' s)
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
       lift_result R_ok R_term
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
      (?e. run_function fuel ctx fn1 s = Error e) \/
      lift_result R_ok R_term
        (run_function fuel ctx fn1 s)
        (run_function fuel ctx fn2 s)
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
      run_block fuel ctx bb s = OK v /\
      i < LENGTH bb.bb_instructions /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
      sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  ACCEPT_TAC transfer_sound_exit
QED

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
    run_block fuel ctx bb s = OK v
    ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  ACCEPT_TAC analysisSimProofsTheory.successor_in_cfg_dfs_pre
QED
