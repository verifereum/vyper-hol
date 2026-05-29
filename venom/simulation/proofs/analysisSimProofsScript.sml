(*
 * Analysis-Driven Simulation — Proofs (Part 1: Transfer Soundness)
 *
 * Core theorems:
 *   cfg_dfs_pre_succs_closed, transfer_sound_step, transfer_sound_exit,
 *   transfer_sound_exit_wf, transfer_sound_exit_wf_len, term_step_base_idx_0
 *   run_block_OK_not_halted, run_block_OK_inst_idx_0,
 *   eval_phis_OK_run_block_eq, run_block_eval_phis_Error
 *
 * Other parts split into separate files to avoid OOM:
 *   analysisSimProofsSound  — sound/widen sound correctness proofs
 *   analysisSimProofsPrepend — prepend correctness proofs
 *   analysisSimProofsFwd     — forward analysis / transform comparison proofs
 *
 * Depends on analysisSimProofsBase for all shared helpers.
 *)

Theory analysisSimProofs
Ancestors
  analysisSimProofsBase analysisSimProofsCompare
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState venomWf cfgAnalysisProps execEquivProofs
  list finite_map pred_set string

(* Successors of cfg_dfs_pre labels are in cfg_dfs_pre.
   Follows from dfs_pre_walk_closure + dfs_pre_walk_visited_eq. *)
Theorem cfg_dfs_pre_succs_closed:
  !fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    EVERY (\t. MEM t (cfg_analyze fn).cfg_dfs_pre)
          (cfg_succs_of (cfg_analyze fn) lbl)
Proof
  rw[cfgDefsTheory.cfg_analyze_def, cfgDefsTheory.cfg_succs_of_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  Cases_on `entry_block fn` >> gvs[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  qabbrev_tac `succs = build_succs fn.fn_blocks` >>
  qabbrev_tac `entry = x.bb_label` >>
  `MEM lbl (SND (dfs_pre_walk succs [] entry))` by gvs[] >>
  `MEM t (FST (dfs_pre_walk succs [] entry))` by
    metis_tac[cj 1 cfgHelpersTheory.dfs_pre_walk_closure] >>
  `set _0 = set pre` by (
    `set (FST (dfs_pre_walk succs [] entry)) =
     set [] UNION set (SND (dfs_pre_walk succs [] entry))` by
      metis_tac[cj 1 cfgHelpersTheory.dfs_pre_walk_visited_eq] >>
    gvs[]) >>
  `MEM t _0` by gvs[] >>
  metis_tac[]
QED

(* df_process_block never modifies ds_inst (only ds_boundary) *)
Triviality df_process_block_keys:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st k.
    k IN FDOM (df_process_block dir bottom join transfer edge_transfer
                 ctx entry_val cfg bbs lbl st).ds_inst ==>
    FST k = lbl \/ k IN FDOM st.ds_inst
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `k IN _` mp_tac >>
  simp[df_process_block_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

(* Two-sided join FOLDL soundness: when all list elements are
   universally sound and join preserves soundness from both sides. *)
Triviality foldl_sound_two_sided:
  !l (bottom : 'a) join sound.
    (!s. sound bottom s) /\
    (!a b s. sound a s /\ sound b s ==> sound (join a b) s) /\
    EVERY (\v. !s. sound v s) l ==>
    !s. sound (FOLDL join bottom l) s
Proof
  Induct
  >- (rpt strip_tac >> simp_tac (srw_ss()) [] >>
      qpat_x_assum `!s. sound bottom s` (fn th => ACCEPT_TAC (SPEC_ALL th)))
  >> rpt strip_tac >> simp_tac (srw_ss()) [] >>
  first_x_assum irule >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> qpat_assum `!a b s. _` irule >> rpt conj_tac
      >- (qpat_x_assum `!s. sound bottom s`
            (fn th => ACCEPT_TAC (SPEC_ALL th)))
      >> qpat_x_assum `EVERY _ _` mp_tac >>
      simp_tac (srw_ss()) [] >> strip_tac >>
      qpat_x_assum `!s. sound h s` (fn th => ACCEPT_TAC (SPEC_ALL th)))
  >> qpat_x_assum `EVERY _ _` mp_tac >>
  simp_tac (srw_ss()) []
QED

(* Transfer-sound chain: running original block from sound entry gives
   sound exit value. Uses the same idx-0 trick as analysis_block_sim. *)
(* Helper: terminator step_inst_base is idx-independent for OK results *)
Theorem term_step_base_idx_0:
  !inst s v.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK v ==>
    step_inst_base inst (s with vs_inst_idx := 0) = OK v
Proof
  rpt strip_tac >>
  `v.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  qabbrev_tac `f = \st:venom_state. st with vs_inst_idx := 0` >>
  `exec_result_map f (step_inst_base inst (s with vs_inst_idx := 0)) =
   exec_result_map f (step_inst_base inst s)` by
    (unabbrev_all_tac >>
     metis_tac[instIdxIndepTheory.terminator_step_inst_base_idx_norm0]) >>
  `exec_result_map f (step_inst_base inst s) = OK v` by
    (simp[Abbr `f`, instIdxIndepTheory.exec_result_map_def] >>
     `v with vs_inst_idx := 0 = v` by
       simp[venom_state_component_equality] >> fs[]) >>
  fs[] >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := 0)` >>
  fs[Abbr `f`, instIdxIndepTheory.exec_result_map_def] >>
  `v'.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  fs[venom_state_component_equality]
QED

(* Helper: apply transfer_sound to get soundness at SUC idx *)
Theorem transfer_sound_step:
  !sound transfer run_ctx inst fuel ctx s s' v_in v_out.
    transfer_sound sound transfer run_ctx /\
    sound v_in s /\
    step_inst fuel ctx inst s = OK s' /\
    v_out = transfer run_ctx inst v_in ==>
    sound v_out s'
Proof
  rw[transfer_sound_def] >> res_tac
QED

(* Transfer-sound chain through a block: running the original block from
   a state where sound(df_at lbl idx) gives sound(df_at lbl (SUC exit_idx))
   at the exit state. The exit index is wherever exec_block terminates.
   
   Note: concludes at SUC of the terminator index, NOT at LENGTH.
   For well-formed blocks where the terminator is last, SUC exit = LENGTH. *)
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
  rpt strip_tac >>
  `!n fuel ctx s.
     n = i + 1 - s.vs_inst_idx /\
     s.vs_inst_idx <= i /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) /\
     exec_block fuel ctx bb s = OK v ==>
     sound (df_at bottom result bb.bb_label (SUC i)) v`
    suffices_by (
      disch_then (qspecl_then
        [`i + 1`, `fuel`, `ctx`, `s`] mp_tac) >>
      `s with vs_inst_idx := 0 = s` by
        fs[venom_state_component_equality] >> simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `idx = s'.vs_inst_idx` >>
  `idx < LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `exec_block fuel' ctx' bb s' =
   case step_inst fuel' ctx' inst s' of
     OK s'' =>
       if is_terminator inst.inst_opcode then
         if s''.vs_halted then Halt s'' else OK s''
       else exec_block fuel' ctx' bb (s'' with vs_inst_idx := SUC idx)
   | Halt s'' => Halt s''
   | Abort a s'' => Abort a s''
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  Cases_on `step_inst fuel' ctx' inst s'` >> fs[]
  >- (
    rename1 `OK s''` >>
    Cases_on `idx = i`
    >- (
      (* At the terminator index: idx = i *)
      `is_terminator inst.inst_opcode` by fs[Abbr `inst`] >>
      Cases_on `s''.vs_halted` >- fs[] >>
      (* Non-halted: fs[] applies intra_fwd, rewrites df_at(SUC i) to
         transfer run_ctx inst (df_at lbl i). Also s'' = v. *)
      fs[] >>
      (* Goal: sound (transfer run_ctx inst (df_at lbl i)) v *)
      (* Use transfer_sound: need step_inst at idx=0 *)
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> fs[is_terminator_def]) >>
      `step_inst_base inst s' = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `step_inst_base inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[term_step_base_idx_0] >>
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[step_inst_non_invoke] >>
      metis_tac[transfer_sound_def]
    )
    >- (
      (* Before the terminator: step through non-terminator, advance idx *)
      `idx < i` by decide_tac >>
      `~is_terminator inst.inst_opcode` by
        (qpat_x_assum `!j. j < i ==> _` (qspec_then `idx` mp_tac) >>
         simp[Abbr `inst`]) >>
      fs[] >>
      (* Normalize step_inst to idx=0 *)
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) =
       OK (s'' with vs_inst_idx := 0)` by (
        Cases_on `inst.inst_opcode = INVOKE`
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only) >>
            simp[])
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.step_inst_idx_indep) >>
            simp[instIdxIndepTheory.exec_result_map_def])) >>
      (* Derive soundness at SUC idx *)
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      `sound (df_at bottom result bb.bb_label (SUC idx))
             (s'' with vs_inst_idx := 0)` by
        metis_tac[transfer_sound_def, markerTheory.Abbrev_def] >>
      (* Apply IH *)
      first_x_assum (qspec_then `i + 1 - SUC idx` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `s'' with vs_inst_idx := SUC idx`] mp_tac) >>
      simp[] >>
      metis_tac[transfer_sound_def, markerTheory.Abbrev_def]
    )
  )
QED

(* Like transfer_sound_exit but uses transfer_sound_wf + EVERY inst_wf.
   Useful when the soundness predicate needs inst_wf to derive facts
   about operand well-formedness (e.g. operands in FDOM). *)
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
  rpt strip_tac >>
  `!n fuel ctx s.
     n = i + 1 - s.vs_inst_idx /\
     s.vs_inst_idx <= i /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) /\
     exec_block fuel ctx bb s = OK v ==>
     sound (df_at bottom result bb.bb_label (SUC i)) v`
    suffices_by (
      disch_then (qspecl_then
        [`i + 1`, `fuel`, `ctx`, `s`] mp_tac) >>
      `s with vs_inst_idx := 0 = s` by
        fs[venom_state_component_equality] >> simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `idx = s'.vs_inst_idx` >>
  `idx < LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst_wf inst` by metis_tac[EVERY_EL, markerTheory.Abbrev_def] >>
  `exec_block fuel' ctx' bb s' =
   case step_inst fuel' ctx' inst s' of
     OK s'' =>
       if is_terminator inst.inst_opcode then
         if s''.vs_halted then Halt s'' else OK s''
       else exec_block fuel' ctx' bb (s'' with vs_inst_idx := SUC idx)
   | Halt s'' => Halt s''
   | Abort a s'' => Abort a s''
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  Cases_on `step_inst fuel' ctx' inst s'` >> fs[]
  >- (
    rename1 `OK s''` >>
    Cases_on `idx = i`
    >- (
      `is_terminator inst.inst_opcode` by fs[Abbr `inst`] >>
      Cases_on `s''.vs_halted` >- fs[] >>
      fs[] >>
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> fs[is_terminator_def]) >>
      `step_inst_base inst s' = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `step_inst_base inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[term_step_base_idx_0] >>
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[step_inst_non_invoke] >>
      metis_tac[transfer_sound_wf_def]
    )
    >- (
      `idx < i` by decide_tac >>
      `~is_terminator inst.inst_opcode` by
        (qpat_x_assum `!j. j < i ==> _` (qspec_then `idx` mp_tac) >>
         simp[Abbr `inst`]) >>
      fs[] >>
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) =
       OK (s'' with vs_inst_idx := 0)` by (
        Cases_on `inst.inst_opcode = INVOKE`
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only) >>
            simp[])
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.step_inst_idx_indep) >>
            simp[instIdxIndepTheory.exec_result_map_def])) >>
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      `sound (df_at bottom result bb.bb_label (SUC idx))
             (s'' with vs_inst_idx := 0)` by
        metis_tac[transfer_sound_wf_def, markerTheory.Abbrev_def] >>
      first_x_assum (qspec_then `i + 1 - SUC idx` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `s'' with vs_inst_idx := SUC idx`] mp_tac) >>
      simp[] >>
      metis_tac[transfer_sound_wf_def, markerTheory.Abbrev_def]
    )
  )
  >> fs[AllCaseEqs()]
QED

(* Like transfer_sound_exit_wf but derives the terminator index from
   bb_well_formed, concluding at LENGTH bb.bb_instructions. *)
Theorem transfer_sound_exit_wf_len:
  !R_ok R_term sound transfer run_ctx bb bottom result.
    valid_state_rel R_ok R_term /\
    transfer_sound_wf sound transfer run_ctx /\
    EVERY inst_wf bb.bb_instructions /\
    bb_well_formed bb /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s v.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      exec_block fuel ctx bb s = OK v ==>
      sound (df_at bottom result bb.bb_label (LENGTH bb.bb_instructions)) v
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `is_terminator
    (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode` by
    (fs[bb_well_formed_def] >>
     Cases_on `bb.bb_instructions` >> fs[listTheory.LAST_EL]) >>
  `!j. j < PRE (LENGTH bb.bb_instructions) ==>
    ~is_terminator (EL j bb.bb_instructions).inst_opcode` by
    (fs[bb_well_formed_def] >>
     rpt strip_tac >> CCONTR_TAC >> fs[] >> res_tac >> fs[]) >>
  `sound (df_at bottom result bb.bb_label
      (SUC (PRE (LENGTH bb.bb_instructions)))) v` suffices_by metis_tac[] >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] transfer_sound_exit_wf) >>
  simp[] >> metis_tac[]
QED
(* Like transfer_sound_exit_wf but starts from arbitrary vs_inst_idx,
   not just 0. Needed for parallel PHI semantics where exec_block
   starts at phi_prefix_length after eval_phis. *)
Theorem transfer_sound_exit_from_wf_ind:
  !R_ok R_term sound transfer run_ctx bb bottom result i v.
    valid_state_rel R_ok R_term /\
    transfer_sound_wf sound transfer run_ctx /\
    EVERY inst_wf bb.bb_instructions /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    i < LENGTH bb.bb_instructions /\
    is_terminator (EL i bb.bb_instructions).inst_opcode /\
    (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode)
    ==>
      !n fuel ctx s.
        n = i + 1 - s.vs_inst_idx /\
        s.vs_inst_idx <= i /\
        sound (df_at bottom result bb.bb_label s.vs_inst_idx)
              (s with vs_inst_idx := 0) /\
        exec_block fuel ctx bb s = OK v ==>
        sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  rpt gen_tac >> strip_tac >>
(* MERGE NOTE: origin/main conflict hunk here contained a block/function
   simulation proof mentioning variables such as s1/s2/bt/fn, which do not
   match transfer_sound_exit_from_wf_ind's statement. Kept the eval-phis proof
   for this induction theorem. If function-level simulation fails later, inspect
   origin/main analysisSimProofsScript.sml around the corresponding theorem and
   port that proof into the right location. *)
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `idx = s.vs_inst_idx` >>
  `idx < LENGTH bb.bb_instructions` by (fs[Abbr `idx`] >> decide_tac) >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst_wf inst` by metis_tac[EVERY_EL, markerTheory.Abbrev_def] >>
  `exec_block fuel ctx bb s =
   case step_inst fuel ctx inst s of
     OK s'' =>
       if is_terminator inst.inst_opcode then
         if s''.vs_halted then Halt s'' else OK s''
       else exec_block fuel ctx bb (s'' with vs_inst_idx := SUC idx)
   | Halt s'' => Halt s''
   | Abort a s'' => Abort a s''
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  Cases_on `step_inst fuel ctx inst s` >> fs[]
  >- (
    rename1 `OK s''` >>
    Cases_on `idx = i`
    >- (
      `is_terminator inst.inst_opcode` by fs[Abbr `inst`] >>
      Cases_on `s''.vs_halted` >- fs[] >>
      fs[] >>
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> fs[is_terminator_def]) >>
      `step_inst_base inst s = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `step_inst_base inst (s with vs_inst_idx := 0) = OK v` by
        metis_tac[term_step_base_idx_0] >>
      `step_inst fuel ctx inst (s with vs_inst_idx := 0) = OK v` by
        metis_tac[step_inst_non_invoke] >>
      metis_tac[transfer_sound_wf_def]
    )
    >- (
      `idx < i` by decide_tac >>
      `~is_terminator inst.inst_opcode` by
        (qpat_x_assum `!j. j < i ==> _` (qspec_then `idx` mp_tac) >>
         simp[Abbr `inst`]) >>
      fs[] >>
      `step_inst fuel ctx inst (s with vs_inst_idx := 0) =
       OK (s'' with vs_inst_idx := 0)` by (
        Cases_on `inst.inst_opcode = INVOKE`
        >- (mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `0`]
              analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only) >>
            simp[])
        >- (mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `0`]
              analysisSimProofsBaseTheory.step_inst_idx_indep) >>
            simp[instIdxIndepTheory.exec_result_map_def])) >>
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      `sound (df_at bottom result bb.bb_label (SUC idx))
             (s'' with vs_inst_idx := 0)` by
        metis_tac[transfer_sound_wf_def, markerTheory.Abbrev_def] >>
      qpat_x_assum `!m. m < _ ==> _` (qspec_then `i + 1 - SUC idx` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel`, `ctx`,
        `s'' with vs_inst_idx := SUC idx`] mp_tac) >>
      simp[] >>
      metis_tac[transfer_sound_wf_def, markerTheory.Abbrev_def]
    )
  )
  >> fs[AllCaseEqs()]

QED

Theorem transfer_sound_exit_from_wf:
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
      s.vs_inst_idx <= i /\
      i < LENGTH bb.bb_instructions /\
      sound (df_at bottom result bb.bb_label s.vs_inst_idx)
            (s with vs_inst_idx := 0) /\
      exec_block fuel ctx bb s = OK v /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
      sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `transfer`, `run_ctx`,
                    `bb`, `bottom`, `result`, `i`, `v`]
    transfer_sound_exit_from_wf_ind) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`i + 1 - s.vs_inst_idx`, `fuel`, `ctx`, `s`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem transfer_sound_exit_from_wf_len:
  !R_ok R_term sound transfer run_ctx bb bottom result.
    valid_state_rel R_ok R_term /\
    transfer_sound_wf sound transfer run_ctx /\
    EVERY inst_wf bb.bb_instructions /\
    bb_well_formed bb /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s v.
      s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
      sound (df_at bottom result bb.bb_label s.vs_inst_idx)
            (s with vs_inst_idx := 0) /\
      exec_block fuel ctx bb s = OK v ==>
      sound (df_at bottom result bb.bb_label (LENGTH bb.bb_instructions)) v
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `is_terminator
    (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode` by
    (fs[bb_well_formed_def] >>
     Cases_on `bb.bb_instructions` >> fs[listTheory.LAST_EL]) >>
  `!j. j < PRE (LENGTH bb.bb_instructions) ==>
    ~is_terminator (EL j bb.bb_instructions).inst_opcode` by
    (fs[bb_well_formed_def] >>
     rpt strip_tac >> CCONTR_TAC >> fs[] >> res_tac >> fs[]) >>
  `sound (df_at bottom result bb.bb_label
      (SUC (PRE (LENGTH bb.bb_instructions)))) v` suffices_by metis_tac[] >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] transfer_sound_exit_from_wf) >>
  simp[] >> metis_tac[]
QED

(* ===== run_block boundary lemmas ===== *)

Theorem run_block_OK_not_halted:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >> strip_tac >>
  fs[run_block_def] >>
  metis_tac[venomExecProofsTheory.exec_block_OK_not_halted]
QED

Theorem run_block_OK_inst_idx_0:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >> strip_tac >>
  fs[run_block_def] >>
  drule venomExecProofsTheory.exec_block_OK_inst_idx_0 >> simp[]
QED

Theorem run_block_eval_phis_Error:
  !fuel ctx bb s e.
    eval_phis s bb.bb_instructions = Error e ==>
    run_block fuel ctx bb s = Error e
Proof
  rpt strip_tac >> fs[run_block_def]
QED

Theorem eval_phis_OK_run_block_eq:
  !fuel ctx bb s s_phi.
    eval_phis s bb.bb_instructions = OK s_phi ==>
    run_block fuel ctx bb s = exec_block fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >> fs[run_block_def]
QED
