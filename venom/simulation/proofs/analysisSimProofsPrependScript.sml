(*
 * Analysis-Driven Simulation — Proofs (Part 4: Prepend Correctness)
 *
 * Main theorem:
 *   df_analysis_pass_correct_prepend_proof
 *)

Theory analysisSimProofsPrepend
Ancestors
  analysisSimProofsWiden analysisSimProofsSound analysisSimProofs analysisSimProofsBase analysisSimProofsCompare
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState venomWf cfgAnalysisProps execEquivProofs
  list finite_map pred_set string

(* Forward-specialized dataflow theorems: need intra_fwd for prepend proofs *)
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_intra_transfer_proof));

Triviality abtp_label:
  !bottom result prepend f bb.
    (analysis_block_transform_prepend bottom result prepend f bb).bb_label =
    bb.bb_label
Proof
  simp[analysis_block_transform_prepend_def]
QED

(* Structural: btp.bb_instructions = TAKE pplen bt.bb_instructions ++ prepend ++ DROP pplen bt.bb_instructions
   This is the ONLY place we unfold analysis_block_transform_prepend_def and
   analysis_block_transform_def. All consumers use this structural fact instead. *)
Triviality btp_bb_instructions_eq:
  !bottom (result:'a df_state) prepend f bb.
    (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    TAKE (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions)
         (analysis_block_transform bottom result f bb).bb_instructions ++
    prepend bb.bb_label ++
    DROP (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions)
         (analysis_block_transform bottom result f bb).bb_instructions
Proof
  simp[analysis_block_transform_prepend_def, analysis_block_transform_def]
QED

(* Inserting non-PHI instructions after the PHI prefix preserves phi_prefix_length. *)
Triviality phi_prefix_length_take_drop_insert:
  !l p. EVERY (\i:instruction. i.inst_opcode <> PHI) p ==>
    phi_prefix_length (TAKE (phi_prefix_length l) l ++ p ++ DROP (phi_prefix_length l) l) =
    phi_prefix_length l
Proof
  Induct_on `l` >> rpt strip_tac
  >- (Cases_on `p` >> gvs[phi_prefix_length_def])
  >> Cases_on `h.inst_opcode = PHI`
  >- (gvs[phi_prefix_length_def] >> res_tac)
  >> gvs[phi_prefix_length_def] >> Cases_on `p` >> gvs[phi_prefix_length_def]
QED

(* For i < phi_prefix_length l, EL i of the "insert after prefix" list = EL i l. *)
Triviality EL_take_drop_insert_prefix:
  !l p i. EVERY (\i:instruction. i.inst_opcode <> PHI) p ==>
    i < phi_prefix_length l ==>
    EL i (TAKE (phi_prefix_length l) l ++ p ++ DROP (phi_prefix_length l) l) = EL i l
Proof
  rpt strip_tac >>
  `i < LENGTH (TAKE (phi_prefix_length l) l)` by
    simp[LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le] >>
  simp[listTheory.EL_APPEND_EQN, EL_TAKE]
QED

(* EL for the "prepend" region: phi_prefix_length l <= i < phi_prefix_length l + LENGTH p *)
Triviality EL_take_drop_insert_mid[local]:
  !l p i. EVERY (\i:instruction. i.inst_opcode <> PHI) p ==>
    phi_prefix_length l <= i /\ i < phi_prefix_length l + LENGTH p ==>
    EL i (TAKE (phi_prefix_length l) l ++ p ++ DROP (phi_prefix_length l) l) = EL (i - phi_prefix_length l) p
Proof
  rpt strip_tac >>
  `LENGTH (TAKE (phi_prefix_length l) l) = phi_prefix_length l` by
    simp[LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le] >>
  `i - phi_prefix_length l < LENGTH p` by decide_tac >>
  simp[listTheory.EL_APPEND_EQN] >>
  simp[EL_TAKE]
QED

(* EL for the "suffix" region: i >= phi_prefix_length l + LENGTH p *)
Triviality EL_take_drop_insert_suffix[local]:
  !l p i. EVERY (\i:instruction. i.inst_opcode <> PHI) p ==>
    phi_prefix_length l + LENGTH p <= i /\ i < LENGTH l + LENGTH p ==>
    EL i (TAKE (phi_prefix_length l) l ++ p ++ DROP (phi_prefix_length l) l) =
    EL (i - phi_prefix_length l - LENGTH p) (DROP (phi_prefix_length l) l)
Proof
  rpt strip_tac >>
  `LENGTH (TAKE (phi_prefix_length l) l) = phi_prefix_length l` by
    simp[LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le] >>
  `LENGTH (TAKE (phi_prefix_length l) l ++ p) = phi_prefix_length l + LENGTH p` by simp[] >>
  `i - (phi_prefix_length l + LENGTH p) < LENGTH (DROP (phi_prefix_length l) l)` by (
    simp[LENGTH_DROP, venomExecProofsTheory.phi_prefix_length_le] >>
    decide_tac) >>
  simp[listTheory.EL_APPEND_EQN] >>
  simp[EL_TAKE, EL_DROP]
QED

(* Boundary: EL in the prepend region of analysis_block_transform_prepend.
   No abbreviation expansion needed in consumer proofs. *)
Triviality EL_btp_mid[local]:
  !bottom (result:'a df_state) prepend f bb k.
    EVERY (\i. i.inst_opcode <> PHI) (prepend bb.bb_label) /\
    k < LENGTH (prepend bb.bb_label) ==>
    EL (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions + k)
       (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    EL k (prepend bb.bb_label)
Proof
  rpt strip_tac >>
  qabbrev_tac `l = (analysis_block_transform bottom result f bb).bb_instructions` >>
  qabbrev_tac `p = prepend bb.bb_label` >>
  `EL (phi_prefix_length l + k)
       (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    EL (phi_prefix_length l + k) (TAKE (phi_prefix_length l) l ++ p ++ DROP (phi_prefix_length l) l)` by
    simp[btp_bb_instructions_eq, Abbr `l`, Abbr `p`] >>
  pop_assum SUBST1_TAC >>
  `LENGTH (TAKE (phi_prefix_length l) l) = phi_prefix_length l` by
    simp[LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le] >>
  `phi_prefix_length l + k < phi_prefix_length l + LENGTH p` by simp[Abbr `p`] >>
  simp[listTheory.EL_APPEND_EQN, EL_TAKE]
QED

(* Boundary: EL in the suffix region of analysis_block_transform_prepend. *)
Triviality EL_btp_suffix[local]:
  !bottom (result:'a df_state) prepend f bb k.
    EVERY (\i. i.inst_opcode <> PHI) (prepend bb.bb_label) /\
    k < LENGTH (DROP (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions)
                    (analysis_block_transform bottom result f bb).bb_instructions) ==>
    EL (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions +
        LENGTH (prepend bb.bb_label) + k)
       (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    EL (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions + k)
       (analysis_block_transform bottom result f bb).bb_instructions
Proof
  rpt strip_tac >>
  qabbrev_tac `l = (analysis_block_transform bottom result f bb).bb_instructions` >>
  qabbrev_tac `p = prepend bb.bb_label` >>
  `phi_prefix_length l ≤ LENGTH l` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `LENGTH (DROP (phi_prefix_length l) l) = LENGTH l - phi_prefix_length l` by
    simp[LENGTH_DROP] >>
  `phi_prefix_length l + k < LENGTH l` by decide_tac >>
  `EL (phi_prefix_length l + LENGTH p + k)
       (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    EL (phi_prefix_length l + LENGTH p + k)
       (TAKE (phi_prefix_length l) l ++ p ++ DROP (phi_prefix_length l) l)` by
    simp[btp_bb_instructions_eq, Abbr `l`, Abbr `p`] >>
  pop_assum SUBST1_TAC >>
  `LENGTH (TAKE (phi_prefix_length l) l) = phi_prefix_length l` by
    simp[LENGTH_TAKE_EQ] >>
  `LENGTH (TAKE (phi_prefix_length l) l ++ p) = phi_prefix_length l + LENGTH p` by simp[] >>
  simp[listTheory.EL_APPEND_EQN, EL_TAKE, EL_DROP]
QED

(* Boundary: eval_phis is the same for bt and btp blocks when prepend is non-PHI.
   This composes btp_bb_instructions_eq + phi_prefix_length_take_drop_insert +
   EL_take_drop_insert_prefix + eval_phis_same_phi_prefix into one step. *)
Triviality eval_phis_btp_eq_bt:
  !bottom (result:'a df_state) prepend f bb s.
    EVERY (\i. i.inst_opcode <> PHI) (prepend bb.bb_label) ==>
    eval_phis s (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    eval_phis s (analysis_block_transform bottom result f bb).bb_instructions
Proof
  rpt strip_tac >>
  (* Establish phi_prefix_length equality before EL lemmas *)
  `phi_prefix_length
     (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
   phi_prefix_length
     (analysis_block_transform bottom result f bb).bb_instructions` by (
    simp[btp_bb_instructions_eq] >>
    match_mp_tac phi_prefix_length_take_drop_insert >>
    simp[EVERY_MEM] >> rpt strip_tac >> res_tac >> simp[]) >>
  match_mp_tac venomExecProofsTheory.eval_phis_same_phi_prefix >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  (* KEY: abbreviate complex terms so simp can find the pattern *)
  qabbrev_tac `l = (analysis_block_transform bottom result f bb).bb_instructions` >>
  qabbrev_tac `p = prepend bb.bb_label` >>
  `EL i (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    EL i (TAKE (phi_prefix_length l) l ++ p ++ DROP (phi_prefix_length l) l)` by (
    simp[btp_bb_instructions_eq, Abbr `l`, Abbr `p`]) >>
  simp[EL_take_drop_insert_prefix] >>
  qpat_x_assum `phi_prefix_length _ = phi_prefix_length _` (fn eq =>
    once_rewrite_tac[GSYM eq]) >>
  simp[] >>
  simp[EVERY_MEM, Abbr `p`] >> rpt strip_tac >> res_tac >> simp[]
QED

(* Boundary: phi_prefix_length is the same for bt and btp blocks when prepend is non-PHI. *)
Triviality phi_prefix_length_btp_eq_bt:
  !bottom (result:'a df_state) prepend f bb.
    EVERY (\i. i.inst_opcode <> PHI) (prepend bb.bb_label) ==>
    phi_prefix_length (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[btp_bb_instructions_eq] >>
  match_mp_tac phi_prefix_length_take_drop_insert >>
  first_assum ACCEPT_TAC
QED

(* Helper: EVERY non-PHI from MEM hypothesis *)
Triviality prepend_every_non_phi[local]:
  !(prepend:string->instruction list) lbl.
    (!inst. MEM inst (prepend lbl) ==>
      ~is_terminator inst.inst_opcode /\
      inst.inst_opcode <> INVOKE /\
      inst.inst_opcode <> PHI) ==>
    EVERY (\i. i.inst_opcode <> PHI) (prepend lbl)
Proof
  simp[EVERY_MEM]
QED

(* exec_block_index_shift specialized for the "mid-insert" pattern:
   bb1 = prefix ++ gap ++ suffix, bb2 = prefix ++ suffix,
   exec from offset (into bb2 suffix) and offset+gap (into bb1 suffix) respectively.
   Proof approach: introduce s0 = s with vs_inst_idx := offset, rewrite goal to
   match exec_block_index_shift's conclusion pattern, then apply irule. *)
Triviality exec_block_mid_insert_lift[local]:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   fuel ctx bb1 bb2 offset gap (s : venom_state).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    offset <= LENGTH bb2.bb_instructions /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions + gap /\
    (!k. k < LENGTH (DROP offset bb2.bb_instructions) ==>
         EL (offset + gap + k) bb1.bb_instructions = EL (offset + k) bb2.bb_instructions)
    ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb2 (s with vs_inst_idx := offset))
      (exec_block fuel ctx bb1 (s with vs_inst_idx := offset + gap))
Proof
  rpt strip_tac >>
  qabbrev_tac `s0 = s with vs_inst_idx := offset` >>
  `(s with vs_inst_idx := offset + gap) =
    (s0 with vs_inst_idx := s0.vs_inst_idx + gap)` by
      simp[venom_state_component_equality, Abbr `s0`] >>
  pop_assum SUBST_ALL_TAC >>
  `exec_block fuel ctx bb2 (s with vs_inst_idx := offset) =
    exec_block fuel ctx bb2 s0` by simp[Abbr `s0`] >>
  pop_assum SUBST_ALL_TAC >>
  `s0.vs_inst_idx = offset` by simp[Abbr `s0`] >>
  irule exec_block_index_shift >>
  fs[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`i - offset`] mp_tac) >>
  simp[LENGTH_DROP] >> decide_tac
QED

(* Core block-level lemma: bt bb ~ btp bb when prepend is non-PHI.
   This replaces the 150-line inline by block. *)
Triviality prepend_run_block_lift[local]:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result:'a df_state)
   (prepend : string -> instruction list)
   (f : 'a -> instruction -> instruction list)
   (fn : ir_function)
   (bb : basic_block) (fuel : num) (run_ctx : venom_context) (s2 : venom_state).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    MEM bb fn.fn_blocks /\
    s2.vs_inst_idx = 0 /\
    (!lbl fuel ctx s. s.vs_inst_idx = 0 ==>
      ?s'. run_insts fuel ctx (prepend lbl) s = OK s' /\ R_ok s s') /\
    (!lbl inst. MEM inst (prepend lbl) ==>
      ~is_terminator inst.inst_opcode /\
      inst.inst_opcode <> INVOKE /\
      inst.inst_opcode <> PHI) /\
    (!inst x. MEM inst (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term
      (run_block fuel run_ctx
        (analysis_block_transform bottom result f bb) s2)
      (run_block fuel run_ctx
        (analysis_block_transform_prepend bottom result prepend f bb) s2)
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) (prepend bb.bb_label)` by
    metis_tac[prepend_every_non_phi] >>
  (* Prove concrete EL facts BEFORE abbreviations so boundary lemmas can match *)
  `!k. k < LENGTH (prepend bb.bb_label) ==>
    EL (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions + k)
       (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    EL k (prepend bb.bb_label)` by
    metis_tac[EL_btp_mid] >>
  `!k. k < LENGTH (DROP (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions)
                      (analysis_block_transform bottom result f bb).bb_instructions) ==>
    EL (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions +
        LENGTH (prepend bb.bb_label) + k)
       (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
    EL (phi_prefix_length (analysis_block_transform bottom result f bb).bb_instructions + k)
       (analysis_block_transform bottom result f bb).bb_instructions` by
    metis_tac[EL_btp_suffix] >>
  `eval_phis s2
     (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
   eval_phis s2
     (analysis_block_transform bottom result f bb).bb_instructions` by
    metis_tac[eval_phis_btp_eq_bt] >>
  `phi_prefix_length
     (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions =
   phi_prefix_length
     (analysis_block_transform bottom result f bb).bb_instructions` by
    metis_tac[phi_prefix_length_btp_eq_bt] >>
  qabbrev_tac `bt_bb = analysis_block_transform bottom result f bb` >>
  qabbrev_tac `btp_bb = analysis_block_transform_prepend bottom result prepend f bb` >>
  DISJ_CASES_TAC (ISPECL [``s2:venom_state``, ``bt_bb.bb_instructions``]
    eval_phis_ok_or_error_defs)
  >- (* eval_phis OK case *)
     (qabbrev_tac `pplen = phi_prefix_length bt_bb.bb_instructions` >>
      qpat_x_assum `?s'. eval_phis s2 bt_bb.bb_instructions = OK s'`
        strip_assume_tac >>
      rename1 `eval_phis s2 bt_bb.bb_instructions = OK s_phi` >>
      `eval_phis s2 btp_bb.bb_instructions = OK s_phi` by fs[] >>
      `phi_prefix_length btp_bb.bb_instructions = pplen` by fs[] >>
      `run_block fuel run_ctx bt_bb s2 =
         exec_block fuel run_ctx bt_bb
           (s_phi with vs_inst_idx := pplen)` by
        metis_tac[eval_phis_OK_run_block_eq] >>
      `run_block fuel run_ctx btp_bb s2 =
         exec_block fuel run_ctx btp_bb
           (s_phi with vs_inst_idx := pplen)` by
        metis_tac[eval_phis_OK_run_block_eq] >>
      qabbrev_tac `pfx = prepend bb.bb_label` >>
      `s_phi.vs_inst_idx = 0` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_inst_idx] >>
      `?s'. run_insts fuel run_ctx pfx s_phi = OK s' /\ R_ok s_phi s'` by (
        qpat_x_assum `!lbl fuel ctx s. s.vs_inst_idx = 0 ==>
          ?s'. run_insts fuel ctx (prepend lbl) s = OK s' /\ R_ok s s'`
          (qspecl_then [`bb.bb_label`, `fuel`, `run_ctx`, `s_phi`] mp_tac) >>
        simp[Abbr `pfx`]) >>
      qabbrev_tac `plen = LENGTH pfx` >>
      `LENGTH btp_bb.bb_instructions = LENGTH bt_bb.bb_instructions + plen` by (
        simp[Abbr `plen`, Abbr `btp_bb`, Abbr `bt_bb`,
             btp_bb_instructions_eq, analysis_block_transform_def,
             LENGTH_TAKE_EQ, LENGTH_DROP,
             venomExecProofsTheory.phi_prefix_length_le]) >>
      (* Fold concrete EL facts through abbreviations *)
      `!k. k < LENGTH pfx ==> EL (pplen + k) btp_bb.bb_instructions = EL k pfx` by (
        fs[Abbr `pfx`, Abbr `pplen`, Abbr `bt_bb`, Abbr `btp_bb`]) >>
      `!k. k < LENGTH (DROP pplen bt_bb.bb_instructions) ==>
        EL (pplen + plen + k) btp_bb.bb_instructions =
        EL (pplen + k) bt_bb.bb_instructions` by (
        fs[Abbr `plen`, Abbr `pplen`, Abbr `bt_bb`, Abbr `btp_bb`]) >>
      `exec_block fuel run_ctx btp_bb
           (s_phi with vs_inst_idx := pplen) =
       exec_block fuel run_ctx btp_bb
           (s' with vs_inst_idx := pplen + plen)` by (
        mp_tac (Q.SPECL [`pfx`, `fuel`, `run_ctx`, `btp_bb`, `s_phi`, `pplen`, `s'`]
                   exec_block_skip_prefix) >>
        impl_tac >- (
          rpt conj_tac
          >- (`phi_prefix_length bt_bb.bb_instructions ≤ LENGTH bt_bb.bb_instructions` by
                simp[venomExecProofsTheory.phi_prefix_length_le] >>
              fs[Abbr `pplen`, Abbr `plen`] >> decide_tac)
          >- (simp[Abbr `pfx`, EVERY_MEM] >>
              rpt strip_tac >>
              qpat_x_assum `!lbl inst. MEM inst (prepend lbl) ==>
                ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
                inst.inst_opcode <> PHI`
                (fn th => assume_tac (Q.SPEC `bb.bb_label` th) >> res_tac) >>
              simp[])
          >- first_assum ACCEPT_TAC
          >- (fs[Abbr `pfx`] >> first_assum ACCEPT_TAC)) >>
        simp[Abbr `plen`]) >>
      `pplen <= LENGTH bt_bb.bb_instructions` by
        (fs[Abbr `pplen`] >> simp[venomExecProofsTheory.phi_prefix_length_le]) >>
      `lift_result R_ok R_term R_term
          (exec_block fuel run_ctx bt_bb
             (s_phi with vs_inst_idx := pplen))
          (exec_block fuel run_ctx btp_bb
             (s_phi with vs_inst_idx := pplen + plen))` by (
        mp_tac (Q.SPECL [`R_ok`, `R_term`, `fuel`, `run_ctx`,
                          `btp_bb`, `bt_bb`, `pplen`, `plen`, `s_phi`]
                          exec_block_mid_insert_lift) >>
        impl_tac >- (
          rpt conj_tac
          >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC
          >- fs[]) >>
        simp[]) >>
      `R_ok (s_phi with vs_inst_idx := pplen + plen)
            (s' with vs_inst_idx := pplen + plen)` by
        metis_tac[vsr_inst_idx_R_ok] >>
      `MEM btp_bb (analysis_function_transform_prepend bottom result prepend f fn).fn_blocks` by (
        simp[analysis_function_transform_prepend_def,
             function_map_transform_def, MEM_MAP] >>
        qexists_tac `bb` >> simp[Abbr `btp_bb`]) >>
      `lift_result R_ok R_term R_term
          (exec_block fuel run_ctx btp_bb
             (s_phi with vs_inst_idx := pplen + plen))
          (exec_block fuel run_ctx btp_bb
             (s' with vs_inst_idx := pplen + plen))` by (
        irule exec_block_preserves_R_block >> rpt conj_tac
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC
        >> metis_tac[vsr_inst_idx_R_ok]) >>
      irule lift_result_trans_proof >> fs[] >>
      metis_tac[])
  >- (* eval_phis Error case *)
     (first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
      `run_block fuel run_ctx bt_bb s2 = Error e` by
        metis_tac[run_block_eval_phis_Error] >>
      `eval_phis s2 btp_bb.bb_instructions = Error e` by fs[] >>
      `run_block fuel run_ctx btp_bb s2 = Error e` by
        metis_tac[run_block_eval_phis_Error] >>
      gvs[lift_result_def])
QED


(* Compose analysis + prepend simulation: bb s2 → btp bb s2.
   Takes the Step 2 result (analysis_run_block_sim) as hypothesis
   and composes with prepend_run_block_lift. Clean context — no abbreviations. *)
Triviality analysis_prepend_run_block_sim[local]:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result:'a df_state)
   (prepend : string -> instruction list)
   (f : 'a -> instruction -> instruction list)
   (fn : ir_function)
   (bb : basic_block) (fuel : num) (run_ctx : venom_context) (s2 : venom_state).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    MEM bb fn.fn_blocks /\
    s2.vs_inst_idx = 0 /\
    ((?e. run_block fuel run_ctx bb s2 = Error e) \/
     lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
       (run_block fuel run_ctx (analysis_block_transform bottom result f bb) s2)) /\
    (!lbl fuel ctx s. s.vs_inst_idx = 0 ==>
      ?s'. run_insts fuel ctx (prepend lbl) s = OK s' /\ R_ok s s') /\
    (!lbl inst. MEM inst (prepend lbl) ==>
      ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
      inst.inst_opcode <> PHI) /\
    (!inst x. MEM inst (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
    (?e. run_block fuel run_ctx bb s2 = Error e) \/
    lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
      (run_block fuel run_ctx
        (analysis_block_transform_prepend bottom result prepend f bb) s2)
Proof
  rpt strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >>
  `lift_result R_ok R_term R_term
      (run_block fuel run_ctx (analysis_block_transform bottom result f bb) s2)
      (run_block fuel run_ctx
        (analysis_block_transform_prepend bottom result prepend f bb) s2)` by
    (mp_tac (Q.SPECL [`R_ok`, `R_term`, `bottom`, `result`, `prepend`, `f`,
       `fn`, `bb`, `fuel`, `run_ctx`, `s2`] prepend_run_block_lift) >>
     impl_tac >- (
       rpt conj_tac
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >- first_assum ACCEPT_TAC
       >> fs[]) >>
     disch_then ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`R_ok`, `R_term`, `R_term`] lift_result_trans_proof) >>
  impl_tac >- (
    rpt conj_tac
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC) >>
  disch_then (fn th =>
    qspecl_then [`run_block fuel run_ctx bb s2`,
                 `run_block fuel run_ctx (analysis_block_transform bottom result f bb) s2`,
                 `run_block fuel run_ctx (analysis_block_transform_prepend bottom result prepend f bb) s2`] mp_tac th) >>
  simp[]
QED

(* Prepend-aware pass correctness.
   Extends df_analysis_pass_correct_sound_proof for transforms that
   add new instructions before each block. *)
Theorem df_analysis_pass_correct_prepend_proof:
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
      (* Prepend instructions are non-terminator, non-INVOKE, non-PHI *)
      (!lbl inst. MEM inst (prepend lbl) ==>
         ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
         inst.inst_opcode <> PHI) /\
      (* Operand agreement for full transformed function *)
      (!bb inst x.
         MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (* eval_phis preserves entry-point soundness *)
      (!bb s s_phi.
         MEM bb fn.fn_blocks /\
         eval_phis s bb.bb_instructions = OK s_phi /\
         sound (df_at bottom result bb.bb_label 0) s ==>
         sound (df_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0))
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx fn' s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `result = df_analyze Forward bottom join transfer edge_transfer
    ctx entry_val fn` >>
  qabbrev_tac `bt = analysis_block_transform bottom result f` >>
  qabbrev_tac `btp = analysis_block_transform_prepend bottom result prepend f` >>
  `!b. (bt b).bb_label = b.bb_label` by
    simp[Abbr `bt`, abt_label] >>
  `!b. (btp b).bb_label = b.bb_label` by
    simp[Abbr `btp`, abtp_label] >>
  (* Strengthen: add R_ok s1 s2, sound, MEM as induction invariant *)
  qsuff_tac
    `!fuel run_ctx s1 s2.
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
       MEM s1.vs_current_bb cfg.cfg_dfs_pre /\
       sound (df_at bottom result s1.vs_current_bb 0) s1 ==>
       (?e. run_blocks fuel run_ctx fn s1 = Error e) \/
       lift_result R_ok R_term R_term (run_blocks fuel run_ctx fn s1)
         (run_blocks fuel run_ctx (function_map_transform btp fn) s2)`
  >- (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel`, `ctx'`, `s`, `s`] mp_tac) >>
    impl_tac
    >- (rpt conj_tac
        >- (irule vsr_R_ok_refl >> metis_tac[])
        >- first_assum ACCEPT_TAC
        >- (fs[fn_entry_label_def, Abbr `cfg`] >>
            Cases_on `entry_block fn` >> gvs[] >>
            imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first >>
            metis_tac[rich_listTheory.HEAD_MEM])
        >- metis_tac[]) >>
    simp[analysis_function_transform_prepend_def, Abbr `btp`]) >>
  (* Main fuel induction *)
  Induct_on `fuel`
  >- (simp[run_blocks_def, lift_result_def]) >>
  rpt gen_tac >> strip_tac >>
  `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
   (s1.vs_halted <=> s2.vs_halted)` by
    metis_tac[vsr_R_ok_fields] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  simp[function_map_transform_def, lookup_block_map_proof, abtp_label,
       Abbr `btp`] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  gvs[] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb.bb_label = s2.vs_current_bb` by (
    fs[lookup_block_def, FIND_def] >> Cases_on `z` >> gvs[] >>
    imp_res_tac
      (prove(``!n P (l:'a list) i x. INDEX_FIND n P l = SOME (i,x) ==> P x``,
        Induct_on `l` >> rw[INDEX_FIND_def] >>
        gvs[AllCaseEqs()] >> metis_tac[])) >> gvs[]) >>
  sg `sound (df_at bottom result bb.bb_label 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
        (fn th => irule th) >>
      qexists_tac `s1` >> simp[]) >>
  (* Step 1: R_ok bridge: run_block bb s1 ~ run_block bb s2 *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
    (run_block fuel run_ctx bb s2)` by
    (irule run_block_preserves_R_helper >> metis_tac[]) >>
  (* Block-level facts for block simulation *)
  `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
     df_at bottom result bb.bb_label (SUC idx) =
     transfer ctx (EL idx bb.bb_instructions)
       (df_at bottom result bb.bb_label idx))` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`bottom`, `join`, `transfer`, `edge_transfer`, `ctx`,
       `entry_val`, `fn`, `bb.bb_label`, `bb`, `idx`] intra_fwd) >>
     impl_tac >- gvs[Abbr `result`, Abbr `cfg`] >>
     simp[Abbr `result`]) >>
  `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
     rpt strip_tac >> res_tac) >>
  (* Step 2: Block sim: run_block bb s2 ~ run_block (bt bb) s2 *)
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx (bt bb) s2)` by (
    DISJ_CASES_TAC (ISPECL [``s2:venom_state``, ``bb.bb_instructions``]
      eval_phis_ok_or_error_defs)
    >- (* eval_phis OK case *)
       (first_x_assum strip_assume_tac >>
        rename1 `eval_phis s2 bb.bb_instructions = OK s_phi` >>
        `sound (df_at bottom result bb.bb_label
             (phi_prefix_length bb.bb_instructions))
          (s_phi with vs_inst_idx := 0)` by (
          qpat_x_assum `!bb s s_phi. MEM bb fn.fn_blocks /\
            eval_phis s bb.bb_instructions = OK s_phi /\
            sound (df_at bottom result bb.bb_label 0) s ==>
            sound (df_at bottom result bb.bb_label
                 (phi_prefix_length bb.bb_instructions))
              (s_phi with vs_inst_idx := 0)`
            (qspecl_then [`bb`, `s2`, `s_phi`] mp_tac) >>
          simp[]) >>
        mp_tac analysis_run_block_sim >>
        disch_then (qspecl_then [`R_ok`, `R_term`, `sound`, `f`, `bb`,
          `bottom`, `result`, `transfer`, `ctx`] mp_tac) >>
        impl_tac >- (
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          rpt strip_tac >> fs[transfer_sound_def] >> res_tac) >>
        disch_then (qspecl_then [`fuel`, `run_ctx`, `s2`, `s_phi`] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
        simp_tac std_ss [Abbr `bt`])
    >- (* eval_phis Error case *)
       (disj1_tac >>
        first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
        qexists_tac `e` >>
        ONCE_REWRITE_TAC[run_block_def] >> simp[])) >>
  (* Handle error from Step 2 *)
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[]) >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
    (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  fs[Abbr `bt`] >>
  (* Prepend-specific facts *)
  `MEM (analysis_block_transform_prepend bottom result prepend f bb)
       (analysis_function_transform_prepend bottom result prepend f fn).fn_blocks` by
    (simp[analysis_function_transform_prepend_def,
          function_map_transform_def, MEM_MAP] >>
     qexists_tac `bb` >> simp[]) >>
  `!inst x. MEM inst
       (analysis_block_transform_prepend bottom result prepend f bb).bb_instructions /\
     MEM (Var x) inst.inst_operands ==>
     !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2` by (
    rpt strip_tac >>
    first_x_assum (qspecl_then
      [`analysis_block_transform_prepend bottom result prepend f bb`,
       `inst`, `x`] mp_tac) >>
    impl_tac >- simp[] >> simp[]) >>
  (* Combined Steps 2+3 via analysis_prepend_run_block_sim *)
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx
       (analysis_block_transform_prepend bottom result prepend f bb) s2)` by (
    mp_tac (Q.SPECL [`R_ok`, `R_term`, `bottom`, `result`, `prepend`, `f`,
       `fn`, `bb`, `fuel`, `run_ctx`, `s2`] analysis_prepend_run_block_sim) >>
    impl_tac >- (
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- (disj2_tac >> first_assum ACCEPT_TAC)
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC) >>
    disch_then ACCEPT_TAC) >>
  (* Handle error from combined disjunction *)
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[]) >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
    (run_block fuel run_ctx
      (analysis_block_transform_prepend bottom result prepend f bb) s2)` by metis_tac[] >>
  (* Compose: bb s1 ~ btp s2 via transitivity *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
    (run_block fuel run_ctx
      (analysis_block_transform_prepend bottom result prepend f bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel run_ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  (* Case split on run_block results for IH *)
  Cases_on `run_block fuel run_ctx bb s1` >>
  Cases_on `run_block fuel run_ctx
    (analysis_block_transform_prepend bottom result prepend f bb) s2` >>
  gvs[lift_result_def]
  >- (
    rename1 `R_ok v1 v2` >>
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
    `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields] >>
    `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
     sound (df_at bottom result v1.vs_current_bb 0) v1` by metis_tac[] >>
    REWRITE_TAC [GSYM function_map_transform_def] >>
    first_x_assum irule >> simp[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
  >> (
    Cases_on `run_block fuel run_ctx bb s2` >> gvs[lift_result_def] >>
    Cases_on `run_block fuel run_ctx
      (analysis_block_transform_prepend bottom result prepend f bb) s2` >> gvs[lift_result_def])
QED
