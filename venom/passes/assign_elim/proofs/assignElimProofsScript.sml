(*
 * Assign Elimination — Proofs
 *
 * Three-phase decomposition + composition.
 * Phase 1: operand substitution gives equality (copy_sound)
 * Phase 2: NOP dead writes gives state_equiv elim (error disjunct)
 * Phase 3: clear_nops gives equality
 *)

Theory assignElimProofs
Ancestors
  assignElimDefs analysisSimProps analysisSimProofsBase
  passSimulationProps passSimulationProofs venomWf
  passSharedProps venomInstProps dfAnalyzeProofs cfgHelpers
  cfgAnalysisProps

open assignElimDefsTheory passSharedDefsTheory passSharedPropsTheory
     venomStateTheory venomWfTheory venomInstPropsTheory
     analysisSimDefsTheory analysisSimPropsTheory
     passSimulationPropsTheory passSimulationDefsTheory
     stateEquivTheory stateEquivPropsTheory
     execEquivParamDefsTheory execEquivParamPropsTheory
     venomExecSemanticsTheory venomExecProofsTheory finite_mapTheory
     listTheory pred_setTheory venomInstTheory
     latticeDefsTheory dfAnalyzeDefsTheory dfAnalyzeProofsTheory
     cfgHelpersTheory worklistDefsTheory arithmeticTheory
     analysisSimProofsBaseTheory passSimulationProofsTheory
     execEquivParamProofsTheory

(* ===== Proof predicate ===== *)

Definition copy_sound_def:
  copy_sound (copies : copy_lattice) (s : venom_state) <=>
    !x op. FLOOKUP copies x = SOME op ==>
      FLOOKUP s.vs_vars x = eval_operand op s
End

Definition copy_sound_opt_def:
  copy_sound_opt c_opt s <=>
    case c_opt of NONE => T | SOME c => copy_sound c s
End

(* ===== Generic helpers ===== *)

(* run_insts on a singleton equals step_inst *)
Theorem run_insts_sing[local]:
  !fuel ctx inst s.
    run_insts fuel ctx [inst] s = step_inst fuel ctx inst s
Proof
  rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[run_insts_def]
QED

(* lift_result reflexive for reflexive relations *)
Theorem lift_result_eq[local]:
  !R_ok R_term r.
    (!s. R_ok s s) /\ (!s. R_term s s) ==>
    lift_result R_ok R_term r r
Proof
  rpt strip_tac >>
  Cases_on `r` >> simp[lift_result_def]
QED

(* copy_sound_opt + unwrap_copies lookup → eval equality *)
Theorem copy_sound_opt_eval[local]:
  !v s x op.
    copy_sound_opt v s /\
    FLOOKUP (unwrap_copies v) x = SOME op ==>
    eval_operand op s = eval_operand (Var x) s
Proof
  rpt strip_tac >>
  fs[copy_sound_opt_def, unwrap_copies_def] >>
  Cases_on `v` >> fs[copy_sound_def] >>
  res_tac >>
  simp[Once eval_operand_def, lookup_var_def]
QED

(* Outputs of forwardable ASSIGNs in fn are in assign_elim_eliminated_vars *)
Theorem forwardable_output_in_elim[local]:
  !fn pv bb inst out.
    pv = phi_used_vars fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_forwardable_assign pv inst /\
    MEM out inst.inst_outputs ==>
    out IN assign_elim_eliminated_vars fn
Proof
  rw[assign_elim_eliminated_vars_def] >>
  simp[MEM_FLAT, MEM_MAP] >>
  qexists_tac `FLAT (MAP (\inst'.
    if is_forwardable_assign (phi_used_vars fn) inst'
    then inst'.inst_outputs else []) bb.bb_instructions)` >>
  conj_tac >- (qexists_tac `bb` >> simp[]) >>
  simp[MEM_FLAT, MEM_MAP] >>
  qexists_tac `inst.inst_outputs` >> simp[] >>
  qexists_tac `inst` >> simp[]
QED

(* ===== Phase 1: Per-instruction substitution correctness ===== *)

Theorem assign_subst_step_correct:
  !v fuel ctx inst s.
    copy_sound_opt v s /\ inst_wf inst ==>
    step_inst fuel ctx (assign_subst_inst v inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >-
    fs[assign_subst_inst_def] >>
  `assign_subst_inst v inst =
   subst_operands_map (unwrap_copies v) inst` by (
    simp[assign_subst_inst_def, subst_operands_map_def, unwrap_copies_def] >>
    Cases_on `v` >> simp[unwrap_copies_def]
  ) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule subst_operands_map_correct >>
  rpt strip_tac >> fs[] >>
  metis_tac[copy_sound_opt_eval]
QED

(* ===== Phase 2: Dead-write removal ===== *)

(* assign_subst_inst preserves opcode *)
Theorem assign_subst_inst_opcode[local]:
  !v inst. (assign_subst_inst v inst).inst_opcode = inst.inst_opcode
Proof
  rw[assign_subst_inst_def]
QED

(* ASSIGN step_inst only returns OK or Error *)
Theorem step_inst_assign_cases[local]:
  !fuel ctx inst s.
    inst.inst_opcode = ASSIGN ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `step_inst fuel ctx inst s = step_inst_base inst s`
    by metis_tac[step_inst_non_invoke] >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[]
QED

(* Per-instruction: substituted ASSIGN vs NOP gives state_equiv or error *)
Theorem assign_nop_per_inst[local]:
  !fn bb idx fuel ctx s.
    MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions ==>
    let inst = EL idx bb.bb_instructions in
    let v = df_at NONE (copy_prop_analyze fn) bb.bb_label idx in
    (?e. step_inst fuel ctx (assign_subst_inst v inst) s = Error e) \/
    lift_result (state_equiv (assign_elim_eliminated_vars fn))
      (execution_equiv (assign_elim_eliminated_vars fn))
      (step_inst fuel ctx (assign_subst_inst v inst) s)
      (step_inst fuel ctx (assign_elim_inst (phi_used_vars fn) v inst) s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  qabbrev_tac `v = df_at NONE (copy_prop_analyze fn) bb.bb_label idx` >>
  Cases_on `inst.inst_opcode = PHI` >- (
    simp[assign_subst_inst_def, assign_elim_inst_def] >>
    DISJ2_TAC >> irule lift_result_eq >>
    simp[state_equiv_refl, execution_equiv_refl]
  ) >>
  Cases_on `is_forwardable_assign (phi_used_vars fn) inst` >- (
    (* Forwardable ASSIGN: subst keeps ASSIGN, elim gives NOP *)
    simp[assign_elim_inst_def] >>
    `(mk_nop_inst inst).inst_opcode = NOP` by simp[mk_nop_inst_def] >>
    `step_inst fuel ctx (mk_nop_inst inst) s = OK s`
      by metis_tac[step_nop_identity] >>
    simp[] >>
    `inst.inst_opcode = ASSIGN` by fs[is_forwardable_assign_def] >>
    `(assign_subst_inst v inst).inst_opcode = ASSIGN`
      by simp[assign_subst_inst_opcode] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `assign_subst_inst v inst`, `s`]
            step_inst_assign_cases) >> simp[] >>
    strip_tac >- (
      (* OK case: need state_equiv elim s' s *)
      simp[lift_result_def] >>
      `is_effect_free_op (assign_subst_inst v inst).inst_opcode` by
        simp[is_effect_free_op_def] >>
      `state_equiv (set (assign_subst_inst v inst).inst_outputs) s s'` by
        metis_tac[step_effect_free_state_equiv] >>
      `(assign_subst_inst v inst).inst_outputs = inst.inst_outputs` by
        simp[assign_subst_inst_def] >>
      irule state_equiv_sym >> irule state_equiv_subset >>
      qexists_tac `set inst.inst_outputs` >> fs[] >>
      rw[SUBSET_DEF] >>
      `MEM inst bb.bb_instructions` by (
        simp[Abbr `inst`, MEM_EL] >> qexists_tac `idx` >> simp[]
      ) >>
      metis_tac[forwardable_output_in_elim]
    ) >>
    (* Error case *)
    simp[]
  ) >>
  (* Non-forwardable, non-PHI: both apply same substitution *)
  simp[assign_elim_inst_def, assign_subst_inst_def] >>
  DISJ2_TAC >> irule lift_result_eq >>
  simp[state_equiv_refl, execution_equiv_refl]
QED

Theorem assign_elim_inst_structural[local]:
  !pv. inst_transform_structural (\v inst. [assign_elim_inst pv v inst])
Proof
  rw[inst_transform_structural_def] >> rpt conj_tac >> rpt gen_tac >>
  rw[assign_elim_inst_def, LET_THM] >> rpt strip_tac >> (
    TRY (
      `inst.inst_opcode = ASSIGN` by fs[is_forwardable_assign_def] >>
      fs[is_terminator_def]) >>
    TRY (
      `~is_terminator (mk_nop_inst inst).inst_opcode /\
       (mk_nop_inst inst).inst_opcode <> INVOKE` by EVAL_TAC >>
      fs[]))
QED

Theorem assign_nop_dead_writes_correct:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    let pv = phi_used_vars fn in
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    let fn_elim = analysis_function_transform NONE result
                    (\v inst. [assign_elim_inst pv v inst]) fn in
    fn_inst_wf fn /\
    s.vs_inst_idx = 0 /\
    (!bb inst x.
       MEM bb fn_subst.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN elim)
    ==>
    (?e. run_function fuel ctx fn_subst s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn_subst s)
      (run_function fuel ctx fn_elim s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  mp_tac (ISPECL [
    ``state_equiv (assign_elim_eliminated_vars fn)``,
    ``execution_equiv (assign_elim_eliminated_vars fn)``,
    ``NONE : copy_lattice option``,
    ``copy_prop_analyze fn``,
    ``\v inst. [assign_subst_inst v inst]``,
    ``\v inst. [assign_elim_inst (phi_used_vars fn) v inst]``,
    ``fn : ir_function``
  ] analysisSimPropsTheory.analysis_function_transform_compare) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- (
    simp[state_equiv_execution_equiv_valid_state_rel,
         assign_elim_inst_structural,
         inst_transform_structural_def, assign_subst_inst_opcode, EVERY_DEF] >>
    rpt conj_tac
    >- metis_tac[state_equiv_trans]
    >- metis_tac[execution_equiv_trans]
    >- (rpt strip_tac >> simp[run_insts_sing] >>
        metis_tac[assign_nop_per_inst |> SIMP_RULE std_ss [LET_THM]])
    >- (rpt strip_tac >>
        qpat_x_assum `!bb inst x. _` (drule_then (drule_then drule)) >>
        fs[state_equiv_def, execution_equiv_def]))) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

(* ===== Phase 1: Function-level substitution equality ===== *)

(* Analysis convergence properties — standard dataflow obligations.
   These are provable for copy_prop_analyze but tangential to the
   simulation proof. Cheated as local helpers for now; will be proved
   separately as shared infrastructure for all forward analyses. *)

(* Extending a sound copy map with a correct entry *)
Theorem copy_sound_fupdate[local]:
  !copies k v s.
    copy_sound copies s /\
    FLOOKUP s.vs_vars k = eval_operand v s ==>
    copy_sound (copies |+ (k, v)) s
Proof
  rw[copy_sound_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `k = x` >> fs[]
QED

(* Helper: copies' entries are sound after step_inst *)
Theorem copies_restrict_sound[local]:
  !copies killed s s' fuel ctx inst.
    copy_sound copies s /\
    killed = set (inst_defs inst) /\
    step_inst fuel ctx inst s = OK s' /\
    (!v. ~MEM v inst.inst_outputs ==>
         lookup_var v s' = lookup_var v s) ==>
    copy_sound (DRESTRICT copies
                  (COMPL killed INTER
                   COMPL {x | ?y. FLOOKUP (DRESTRICT copies (COMPL killed)) x =
                                    SOME (Var y) /\ y IN killed})) s'
Proof
  rw[copy_sound_def, inst_defs_def] >> rpt strip_tac >>
  fs[FLOOKUP_DRESTRICT] >> rfs[] >>
  `lookup_var x s' = lookup_var x s` by (
    first_x_assum irule >> fs[]) >>
  `FLOOKUP copies x = SOME op` by fs[] >>
  res_tac >>
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def]
QED

(* Terminator OK preserves vars. JMP/JNZI/DJMP only modify
   vs_current_bb/vs_prev_bb/vs_inst_idx, not vs_vars. *)
Theorem step_terminator_preserves_vars[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (
    Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  fs[step_inst_base_def, LET_THM] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >>
       fs[jump_to_def, halt_state_def, revert_state_def,
          set_returndata_def, lookup_var_def]) >>
  rw[]
QED

(* Helper: ASSIGN step semantics *)
Theorem step_assign_result[local]:
  !fuel ctx inst src_op dst s s'.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [src_op] /\
    inst.inst_outputs = [dst] /\
    step_inst fuel ctx inst s = OK s' ==>
    ?val. eval_operand src_op s = SOME val /\
          s' = update_var dst val s
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  pop_assum mp_tac >>
  simp_tac std_ss [Once step_inst_base_def] >>
  Cases_on `eval_operand src_op s` >> simp[]
QED

Theorem copy_prop_transfer_sound[local]:
  !pv. transfer_sound copy_sound_opt
             copy_prop_transfer pv
Proof
  rw[transfer_sound_def] >> rpt strip_tac >>
  Cases_on `v`
  >- (
    (* v = NONE: copies = FEMPTY, all intermediate maps are FEMPTY *)
    simp[copy_sound_opt_def, copy_prop_transfer_def, LET_THM,
         DRESTRICT_FEMPTY] >>
    IF_CASES_TAC >> simp[copy_sound_def, FLOOKUP_SIMP] >>
    (* Forwardable ASSIGN — need copy_sound of FEMPTY |+ (dst, root) *)
    `inst.inst_opcode = ASSIGN` by fs[is_forwardable_assign_def] >>
    `?src_op dst. inst.inst_operands = [src_op] /\
                  inst.inst_outputs = [dst] /\
                  (!l. src_op <> Label l)` by (
      fs[is_forwardable_assign_def] >>
      BasicProvers.every_case_tac >> fs[]) >>
    fs[] >> simp[] >>
    drule_all step_assign_result >> strip_tac >>
    simp[copy_sound_def, FLOOKUP_UPDATE] >>
    rpt strip_tac >> rw[] >>
    simp[update_var_def, FLOOKUP_UPDATE] >>
    Cases_on `src_op` >>
    fs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, update_var_def])
  >- (
    (* v = SOME x: have copy_sound x s, step_inst s = OK s' *)
    fs[copy_sound_opt_def, copy_prop_transfer_def, LET_THM] >>
    `!v. ~MEM v inst.inst_outputs ==>
         lookup_var v s' = lookup_var v s` by (
      Cases_on `is_terminator inst.inst_opcode`
      >- metis_tac[step_terminator_preserves_vars]
      >- metis_tac[step_preserves_non_output_vars]) >>
    IF_CASES_TAC
    >- (
      `inst.inst_opcode = ASSIGN` by fs[is_forwardable_assign_def] >>
      `?src_op dst. inst.inst_operands = [src_op] /\
                    inst.inst_outputs = [dst] /\
                    (!l. src_op <> Label l)` by (
        fs[is_forwardable_assign_def] >>
        BasicProvers.every_case_tac >> fs[]) >>
      fs[] >> simp[] >>
      drule_all step_assign_result >> strip_tac >>
      qabbrev_tac `copies' = DRESTRICT x
         (COMPL (set (inst_defs inst)) INTER
          COMPL {z | ?y. FLOOKUP (DRESTRICT x (COMPL (set (inst_defs inst))))
                            z = SOME (Var y) /\ MEM y (inst_defs inst)})` >>
      `copy_sound copies' (update_var dst val s)` by (
        simp[Abbr `copies'`] >>
        mp_tac (Q.SPECL [`x`, `set (inst_defs inst)`, `s`,
                          `update_var dst val s`, `fuel`, `run_ctx`, `inst`]
                copies_restrict_sound) >>
        impl_tac >- (rw[] >> metis_tac[]) >>
        simp[]) >>
      (* Use copy_sound_fupdate: need eval_operand root s' = FLOOKUP s'.vs_vars dst *)
      irule copy_sound_fupdate >> fs[] >>
      simp[update_var_def, FLOOKUP_UPDATE] >>
      (* Goal: eval root in s' = SOME val, case split on src_op *)
      (* Lit and Label solved by fs; only Var remains *)
      Cases_on `src_op` >> fs[eval_operand_def] >>
      Cases_on `FLOOKUP copies' s''`
      >- ( (* NONE: root = Var v *)
        simp[eval_operand_def, lookup_var_def, update_var_def,
             FLOOKUP_UPDATE] >>
        Cases_on `s'' = dst` >> fs[lookup_var_def])
      >- ( (* SOME r: root = r, use copy_sound copies' s' *)
        `s'' <> dst` by (
          CCONTR_TAC >> fs[] >>
          qpat_x_assum `FLOOKUP copies' _ = SOME _` mp_tac >>
          simp[Abbr `copies'`, FLOOKUP_DRESTRICT, inst_defs_def]) >>
        fs[copy_sound_def] >> res_tac >>
        fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]))
    >- (
      (* Non-forwardable *)
      mp_tac (Q.SPECL [`x`, `set (inst_defs inst)`, `s`, `s'`,
                        `fuel`, `run_ctx`, `inst`]
              copies_restrict_sound) >>
      impl_tac >- (rw[] >> metis_tac[]) >>
      simp[]))
QED

Theorem copy_prop_join_sound[local]:
  !a b s. copy_sound_opt a s /\ copy_sound_opt b s ==>
          copy_sound_opt (copy_prop_join a b) s
Proof
  rpt strip_tac >>
  Cases_on `a` >> Cases_on `b` >>
  fs[copy_sound_opt_def, copy_prop_join_def, copy_sound_def,
     copy_prop_join_raw_def] >>
  rpt strip_tac >>
  fs[FLOOKUP_DRESTRICT]
QED

Theorem copy_sound_opt_fempty[local]:
  !s. copy_sound_opt (SOME FEMPTY) s
Proof
  simp[copy_sound_opt_def, copy_sound_def, FLOOKUP_DEF]
QED

(* Phase 1: substitution gives state_equiv {} at function level.
   Uses the analysis framework with R_ok = state_equiv {}, R_term = execution_equiv {}.
   (Can't use $= directly because valid_state_rel $= $= is false.) *)
(* Inst-level simulation for assign_subst_inst *)
Theorem assign_subst_inst_simulates[local]:
  analysis_inst_simulates (state_equiv {}) (execution_equiv {})
    copy_sound_opt (\v inst. [assign_subst_inst v inst])
Proof
  simp[analysis_inst_simulates_def, inst_transform_structural_def,
       assign_subst_inst_opcode] >>
  rpt strip_tac >> simp[run_insts_sing] >>
  `step_inst fuel ctx (assign_subst_inst v inst) s =
   step_inst fuel ctx inst s`
    by metis_tac[assign_subst_step_correct] >>
  Cases_on `step_inst fuel ctx inst s` >>
  simp[lift_result_def, state_equiv_refl, execution_equiv_refl]
QED

(* copy_sound_opt preserved under state_equiv {} *)
Theorem copy_sound_opt_state_equiv[local]:
  !v s1 s2. state_equiv {} s1 s2 /\ copy_sound_opt v s1 ==>
             copy_sound_opt v s2
Proof
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def, copy_sound_opt_def] >>
  Cases_on `v` >> fs[copy_sound_def] >>
  rpt strip_tac >> res_tac >>
  Cases_on `op` >>
  fs[eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

(* ===== Convergence machinery for copy_prop lattice ===== *)

(* Measure for a single copy_lattice option value.
   NONE = 0 (bottom, no info yet).
   SOME fmap = max_vars + 1 - CARD(FDOM fmap) (under invariant, ≥ 1).
   This INCREASES for both transitions:
   - NONE → SOME fmap: 0 → max+1-CARD ≥ 1
   - SOME big → SOME small: max+1-CARD(big) → max+1-CARD(small), increases
   The second transition corresponds to losing copies (more conservative). *)
Definition copy_val_measure_def:
  copy_val_measure max_vars (NONE : copy_lattice option) = 0 /\
  copy_val_measure max_vars (SOME fmap) = max_vars + 1 - CARD (FDOM fmap)
End
(* Remove from simpset: subtraction causes side conditions that break proofs *)
val _ = delsimps ["copy_val_measure_def"]

(* Invariant: boundary and inst fmap values have FDOM ⊆ fn_all_assignments.
   No FDOM st.ds_inst bound — non-block labels create keys outside
   df_valid_inst_keys, so we can't maintain that invariant (L053). *)
Definition copy_prop_state_inv_def:
  copy_prop_state_inv fn (st : copy_lattice option df_state) <=>
    (!lbl fmap. FLOOKUP st.ds_boundary lbl = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_all_assignments fn)) /\
    (!k fmap. FLOOKUP st.ds_inst k = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_all_assignments fn))
End

(* Extended invariant for convergence proof.
   C1+C2: FDOM bounds (from copy_prop_state_inv)
   C3: fold coherence — ds_inst at lbl keys matches fold from stored v0
   C4: key closure — (lbl,j) in ds_inst implies (lbl,0) in ds_inst
   C5: processed implies boundary exists *)
Definition copy_prop_measure_inv_def:
  copy_prop_measure_inv fn (st : copy_lattice option df_state) <=>
    fn_inst_wf fn /\
    copy_prop_state_inv fn st /\
    (let transfer = copy_prop_transfer (phi_used_vars fn) in
     let instrs_of lbl = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions in
     (* C3: fold coherence *)
     (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
        !k v. FLOOKUP (SND (df_fold_block Forward transfer
                 lbl (instrs_of lbl) v0)) k = SOME v ==>
          FLOOKUP st.ds_inst k = SOME v) /\
     (* C4: key closure *)
     (!lbl j. (lbl, j) IN FDOM st.ds_inst ==>
        (lbl, 0n) IN FDOM st.ds_inst) /\
     (* C5: processed implies boundary exists *)
     (!lbl. (lbl, 0n) IN FDOM st.ds_inst ==>
        lbl IN FDOM st.ds_boundary))
End

(* Boundary measure: sum of per-label boundary-value measures over dfs_pre.
   Covers all labels the worklist might process (not just fn_labels).
   Increases as lattice values move up (NONE→SOME or SOME shrinks). *)
Definition copy_boundary_measure_def:
  copy_boundary_measure fn (st : copy_lattice option df_state) =
    let mv = CARD (set (fn_all_assignments fn)) in
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    SUM (MAP (\lbl. copy_val_measure mv (df_boundary NONE st lbl))
             (fn_labels fn ++ dfs_pre))
End

(* Joined value for copy propagation at a label *)
Definition copy_prop_joined_def:
  copy_prop_joined fn st lbl =
    let cfg = cfg_analyze fn in
    let edge_vals = MAP (\nbr. df_boundary NONE st nbr)
                        (cfg_preds_of cfg lbl) in
    let base = (case edge_vals of
                  [] => NONE
                | _ => FOLDL copy_prop_join NONE edge_vals) in
    case fn_entry_label fn of
      NONE => base
    | SOME ev_lbl =>
        if lbl = ev_lbl then copy_prop_join (SOME FEMPTY) base else base
End

(* Fresh count: number of dfs_pre labels whose stored v0 matches current
   joined value. Covers all worklist-processable labels. *)
Definition copy_prop_fresh_count_def:
  copy_prop_fresh_count fn (st : copy_lattice option df_state) =
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    CARD {lbl | MEM lbl (fn_labels fn ++ dfs_pre) /\
                (lbl, 0n) IN FDOM st.ds_inst /\
                FLOOKUP st.ds_inst (lbl, 0n) =
                SOME (copy_prop_joined fn st lbl)}
End

(* Full measure:
   W * boundary_sum + CARD(valid inst slots filled) + fresh_count + dfs_visited.
   W = all_count + 1 ensures boundary increases dominate fresh decreases.
   all_count = LENGTH(fn_labels ++ dfs_pre) (may count some labels twice,
   but that's fine for bounding — it's a conservative weight).
   fresh_count uses the same all_count list for consistency. *)
Definition copy_prop_measure_def:
  copy_prop_measure fn (st : copy_lattice option df_state) =
    let dfs_pre = (cfg_analyze fn).cfg_dfs_pre in
    let all_count = LENGTH (fn_labels fn) + LENGTH dfs_pre in
    (all_count + 1) * copy_boundary_measure fn st +
    CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) +
    copy_prop_fresh_count fn st +
    CARD (FDOM st.ds_boundary INTER set dfs_pre)
End

(* Upper bound *)
Definition copy_prop_measure_bound_def:
  copy_prop_measure_bound fn =
    let max_vars = CARD (set (fn_all_assignments fn)) in
    let nlabels = LENGTH (fn_labels fn) in
    let total_slots = df_total_inst_slots fn.fn_blocks in
    let ndfs = LENGTH (cfg_analyze fn).cfg_dfs_pre in
    let all_count = nlabels + ndfs in
    (all_count + 1) * ((max_vars + 1) * (nlabels + ndfs)) +
    total_slots +
    (nlabels + ndfs) +
    ndfs
End

(* Per-value measure is bounded under the invariant *)
Theorem copy_val_measure_bounded[local]:
  !v mv.
    (case v of NONE => T
     | SOME fmap => CARD (FDOM fmap) <= mv) ==>
    copy_val_measure mv v <= mv + 1
Proof
  Cases >> simp[copy_val_measure_def]
QED

(* Initial state satisfies copy_prop_state_inv *)
Theorem copy_prop_init_state_inv[local]:
  !fn.
    case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
      NONE => copy_prop_state_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl,v) => copy_prop_state_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary
             |+ (lbl,v))
Proof
  rpt strip_tac >>
  simp[copy_prop_state_inv_def, LET_THM, init_df_state_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >> rpt gen_tac >> strip_tac >> (
    TRY (qpat_x_assum `FLOOKUP (_ |+ _) _ = _`
           (mp_tac o REWRITE_RULE [FLOOKUP_UPDATE]) >>
         IF_CASES_TAC >> simp[] >> strip_tac >> gvs[FDOM_FEMPTY]) >>
    (* FLOOKUP(FOLDL ... FEMPTY labels) _ = SOME v => v = NONE *)
    `SOME fmap = (NONE : copy_lattice option)` by
      metis_tac[dfAnalyzeProofsTheory.foldl_fupdate_flookup,
                FLOOKUP_EMPTY, optionTheory.NOT_SOME_NONE] >>
    fs[])
QED

(* Bound SUM(MAP f l) when each f(x) <= n *)
Triviality sum_map_le_bound[local]:
  !f (n:num) l. EVERY (\x. f x <= n) l ==> SUM (MAP f l) <= n * LENGTH l
Proof
  Induct_on `l` >> rw[] >> res_tac >>
  fs[arithmeticTheory.MULT_SUC]
QED

(* Helper: each boundary value's measure is bounded *)
Triviality copy_val_measure_boundary_le[local]:
  !fn st lbl.
    (!lbl fmap. FLOOKUP st.ds_boundary lbl = SOME (SOME fmap) ==>
       FDOM fmap SUBSET set (fn_all_assignments fn)) ==>
    copy_val_measure (CARD (set (fn_all_assignments fn)))
                     (df_boundary NONE st lbl) <=
    CARD (set (fn_all_assignments fn)) + 1
Proof
  rpt strip_tac >> irule copy_val_measure_bounded >>
  simp[df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[] >>
  Cases_on `x` >> simp[] >>
  res_tac >> irule CARD_SUBSET >> simp[FDOM_FINITE]
QED

(* Measure is bounded under invariant *)
Theorem copy_prop_measure_bounded[local]:
  !fn st.
    copy_prop_state_inv fn st ==>
    copy_prop_measure fn st <= copy_prop_measure_bound fn
Proof
  rpt strip_tac >>
  fs[copy_prop_state_inv_def] >>
  (* Bound 1: boundary measure *)
  `copy_boundary_measure fn st <=
   (CARD (set (fn_all_assignments fn)) + 1) *
   LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` by (
    simp_tac std_ss [copy_boundary_measure_def, LET_THM] >>
    irule arithmeticTheory.LESS_EQ_TRANS >>
    irule_at Any sum_map_le_bound >>
    qexists_tac `CARD (set (fn_all_assignments fn)) + 1` >>
    simp[EVERY_MEM, MEM_APPEND] >>
    rpt strip_tac >> irule copy_val_measure_boundary_le >> metis_tac[]) >>
  fs[LENGTH_APPEND] >>
  (* Bound 2: inst CARD *)
  `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
   (df_total_inst_slots fn.fn_blocks : num)` by (
    match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `CARD (df_valid_inst_keys fn.fn_blocks)` >>
    simp[df_valid_inst_keys_card] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[df_valid_inst_keys_finite]) >>
  (* Bound 3: fresh count *)
  `copy_prop_fresh_count fn st <=
   LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` by (
    simp_tac std_ss [copy_prop_fresh_count_def, LET_THM] >>
    match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `CARD (set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))` >>
    conj_tac >- (
      irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET, SUBSET_DEF]) >>
    simp[CARD_LIST_TO_SET]) >>
  fs[LENGTH_APPEND] >>
  (* Bound 4: dfs_visited *)
  `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
   LENGTH (cfg_analyze fn).cfg_dfs_pre` by (
    match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `CARD (set (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[CARD_LIST_TO_SET] >>
    ONCE_REWRITE_TAC[INTER_COMM] >>
    irule CARD_INTER_LESS_EQ >>
    simp[FINITE_LIST_TO_SET]) >>
  (* Combine: each component bounded, use monotonicity of + and * *)
  simp_tac std_ss [copy_prop_measure_def, copy_prop_measure_bound_def, LET_THM] >>
  irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule arithmeticTheory.LESS_EQ_LESS_EQ_MONO >>
  REVERSE conj_tac >- first_assum ACCEPT_TAC >>
  irule arithmeticTheory.LESS_MONO_MULT2 >> simp[]
QED
(* ===== End convergence helpers ===== *)

(* copy_prop_join is idempotent: join(x,x) = x *)
Theorem copy_prop_join_raw_idem[local]:
  !m. copy_prop_join_raw m m = m
Proof
  rw[copy_prop_join_raw_def, fmap_EXT, DRESTRICT_DEF,
     copy_agree_def, EXTENSION] >>
  rw[FLOOKUP_DRESTRICT] >>
  Cases_on `FLOOKUP m x` >> fs[FLOOKUP_DEF]
QED

(* Unconditional CFG symmetry: succs and preds are inverses by construction.
   Does NOT require wf_function — follows from mem_build_preds + fdom_build_succs. *)
Theorem cfg_edge_symmetry[local]:
  !fn a b. MEM b (cfg_succs_of (cfg_analyze fn) a) <=>
           MEM a (cfg_preds_of (cfg_analyze fn) b)
Proof
  rpt gen_tac >>
  simp[cfgHelpersTheory.cfg_analyze_succs, cfgHelpersTheory.cfg_analyze_preds,
       cfgHelpersTheory.mem_build_preds] >>
  eq_tac >> rpt strip_tac
  >- (
    `?blk. MEM blk fn.fn_blocks /\ blk.bb_label = a` by (
      spose_not_then strip_assume_tac >>
      `~MEM a (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
        simp[MEM_MAP] >> metis_tac[]) >>
      `fmap_lookup_list (build_succs fn.fn_blocks) a = []` by
        metis_tac[cfgHelpersTheory.cfg_succs_of_not_in_labels] >>
      fs[]) >>
    qexists_tac `blk` >> fs[])
  >- metis_tac[]
QED

(* copy_prop_join absorption: join(join(a,b), b) = join(a,b) *)
Theorem copy_prop_join_absorption[local]:
  !a b. copy_prop_join (copy_prop_join a b) b = copy_prop_join a b
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_prop_join_def, copy_prop_join_raw_idem] >>
  rw[copy_prop_join_raw_def, fmap_EXT, DRESTRICT_DEF,
     copy_agree_def, EXTENSION] >>
  rw[FLOOKUP_DRESTRICT]
QED

(* Bridge: df_process_block for copy_prop = fold from copy_prop_joined *)
Triviality copy_prop_process_eq[local]:
  !fn lbl st.
    df_process_block Forward NONE copy_prop_join copy_prop_transfer
      copy_prop_edge_transfer (phi_used_vars fn)
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st =
    let instrs = case lookup_block lbl fn.fn_blocks of
                   NONE => [] | SOME bb => bb.bb_instructions in
    let (fv, inst_map) = df_fold_block Forward
                           (copy_prop_transfer (phi_used_vars fn)) lbl
                           instrs (copy_prop_joined fn st lbl) in
      st with <|ds_boundary := st.ds_boundary |+
                  (lbl, copy_prop_join (df_boundary NONE st lbl) fv);
                ds_inst := FUNION inst_map st.ds_inst|>
Proof
  rw[df_process_block_def, df_joined_val_def] >>
  simp_tac std_ss [LET_THM, direction_case_def] >>
  rw[copy_prop_edge_transfer_def] >>
  simp[copy_prop_joined_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> simp[]
QED

(* copy_prop_join preserves FDOM ⊆ S *)
Triviality copy_prop_join_fdom_subset[local]:
  !c1 c2 bound.
    (case c1 of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    (case c2 of NONE => T | SOME fmap => FDOM fmap SUBSET bound) ==>
    (case copy_prop_join c1 c2 of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  Cases_on `c1` >> Cases_on `c2` >>
  simp[copy_prop_join_def, copy_prop_join_raw_def, FDOM_DRESTRICT] >>
  metis_tac[SUBSET_INTER_ABSORPTION, INTER_SUBSET, SUBSET_TRANS]
QED

(* copy_prop_transfer preserves FDOM ⊆ S when inst outputs ⊆ S.
   Key facts: transfer always returns SOME, DRESTRICT shrinks FDOM,
   FUPDATE adds at most one output variable. *)
Triviality copy_prop_transfer_fdom_subset[local]:
  !ctx inst v bound.
    (case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    set (inst.inst_outputs) SUBSET bound ==>
    (case copy_prop_transfer ctx inst v of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  rpt strip_tac >>
  simp[copy_prop_transfer_def, LET_THM] >>
  (* Result is always SOME, so case eliminates to FDOM ⊆ bound *)
  Cases_on `v` >> simp[] >>
  (* Both branches: IF + nested case on operands/outputs *)
  IF_CASES_TAC >> simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  Cases_on `inst.inst_operands` >>
  simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  Cases_on `inst.inst_outputs` >>
  simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  Cases_on `t` >> simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
  TRY (fs[SUBSET_DEF] >> NO_TAC) >>
  TRY (Cases_on `t'` >> simp[FDOM_DRESTRICT, FDOM_FEMPTY] >>
       TRY (fs[SUBSET_DEF] >> NO_TAC))
QED

(* FOLDL copy_prop_join preserves FDOM ⊆ S *)
Triviality foldl_copy_prop_join_fdom_subset[local]:
  !l init bound.
    (case init of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    EVERY (\v. case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) l ==>
    (case FOLDL copy_prop_join init l of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[copy_prop_join_fdom_subset]
QED

(* df_boundary values satisfy P under invariant *)
Triviality df_boundary_inv[local]:
  !fn st lbl.
    copy_prop_state_inv fn st ==>
    (case df_boundary NONE st lbl of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
Proof
  rpt strip_tac >> simp[df_boundary_def] >>
  CASE_TAC >> simp[] >>
  Cases_on `x` >> simp[] >>
  fs[copy_prop_state_inv_def] >> res_tac
QED

(* Helper: every df_boundary value in a MAP satisfies the invariant *)
Triviality df_boundary_map_inv[local]:
  !fn st lbls.
    copy_prop_state_inv fn st ==>
    EVERY (\v. case v of NONE => T
       | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
      (MAP (\nbr. df_boundary NONE st nbr) lbls)
Proof
  Induct_on `lbls` >> simp[] >> rpt strip_tac >> metis_tac[df_boundary_inv]
QED

(* copy_prop_joined satisfies the invariant *)
Triviality copy_prop_joined_inv[local]:
  !fn st lbl.
    copy_prop_state_inv fn st ==>
    (case copy_prop_joined fn st lbl of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
Proof
  rpt strip_tac >>
  mp_tac (SPECL [``fn : ir_function``, ``st : copy_lattice option df_state``,
                 ``cfg_preds_of (cfg_analyze fn) lbl``]
    df_boundary_map_inv) >>
  simp[] >> strip_tac >>
  simp[copy_prop_joined_def, LET_THM] >>
  (* Prove base has the property, then handle entry wrapping *)
  Cases_on `MAP (\nbr. df_boundary NONE st nbr)
                (cfg_preds_of (cfg_analyze fn) lbl)` >> simp[]
  >- ((* [] case *)
      Cases_on `fn_entry_label fn` >> simp[] >>
      IF_CASES_TAC >> gvs[] >>
      simp[copy_prop_join_def, copy_prop_join_raw_def, FDOM_FEMPTY])
  >- ((* h::t case *)
      Cases_on `fn_entry_label fn` >> simp[]
      >- (match_mp_tac foldl_copy_prop_join_fdom_subset >> fs[] >>
          irule copy_prop_join_fdom_subset >> simp[])
      >- (IF_CASES_TAC >> gvs[]
          >- (irule copy_prop_join_fdom_subset >> simp[FDOM_FEMPTY] >>
              match_mp_tac foldl_copy_prop_join_fdom_subset >> fs[] >>
              irule copy_prop_join_fdom_subset >> simp[])
          >- (match_mp_tac foldl_copy_prop_join_fdom_subset >> fs[] >>
              irule copy_prop_join_fdom_subset >> simp[])))
QED

(* Specialized fold invariant for copy_prop's FDOM property.
   Curried hypotheses for easy use with drule chains. *)
Triviality copy_prop_fold_fdom[local]:
  !transfer lbl instrs init_val fv im bound.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) ==>
    (case init_val of NONE => T
     | SOME fmap => FDOM fmap SUBSET bound) ==>
    (!inst v. MEM inst instrs /\
      (case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound) ==>
      (case transfer inst v of NONE => T | SOME fmap => FDOM fmap SUBSET bound))
    ==>
    (case fv of NONE => T | SOME fmap => FDOM fmap SUBSET bound) /\
    (!k v. FLOOKUP im k = SOME v ==>
      (case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound))
Proof
  rpt strip_tac >>
  drule (dfAnalyzeProofsTheory.df_fold_block_forward_invariant
         |> REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (qspec_then
    `\v. case v of NONE => T | SOME fmap => FDOM fmap SUBSET bound`
    (mp_tac o BETA_RULE)) >>
  simp[] >> strip_tac >> res_tac
QED

(* Transfer preserves FDOM ⊆ bound *)
Triviality copy_prop_transfer_preserves_fdom[local]:
  !fn lbl inst v.
    fn_inst_wf fn /\
    MEM inst (case lookup_block lbl fn.fn_blocks of NONE => []
              | SOME bb => bb.bb_instructions) /\
    (case v of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)) ==>
    (case copy_prop_transfer (phi_used_vars fn) inst v of NONE => T
     | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))
Proof
  rpt strip_tac >>
  irule copy_prop_transfer_fdom_subset >> simp[] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> fs[MEM] >>
  imp_res_tac lookup_block_MEM >>
  simp[SUBSET_DEF] >> rpt strip_tac >>
  simp[fn_all_assignments_def, MEM_nub, MEM_FLAT, MEM_MAP] >>
  simp[PULL_EXISTS] >>
  qexists_tac `x` >> simp[] >>
  simp[inst_defs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

(* P preserved: processing a block preserves the state invariant *)
Triviality copy_prop_inv_preserved[local]:
  !fn lbl st.
    fn_inst_wf fn /\ copy_prop_state_inv fn st ==>
    copy_prop_state_inv fn
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  simp[copy_prop_state_inv_def, copy_prop_process_eq] >>
  simp_tac std_ss [LET_THM] >> pairarg_tac >> simp[] >>
  (* Establish P(joined) *)
  `case copy_prop_joined fn st lbl of NONE => T
   | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)`
    by metis_tac[copy_prop_joined_inv]
  (* Establish transfer preserves P *)
  >> `!inst v.
       MEM inst (case lookup_block lbl fn.fn_blocks of NONE => []
                 | SOME bb => bb.bb_instructions) /\
       (case v of NONE => T
        | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)) ==>
       (case copy_prop_transfer (phi_used_vars fn) inst v of NONE => T
        | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn))`
    by metis_tac[copy_prop_transfer_preserves_fdom]
  (* Apply fold invariant *)
  >> drule copy_prop_fold_fdom
  >> disch_then (qspec_then `set (fn_all_assignments fn)` mp_tac)
  >> simp[]
  >> strip_tac >>
  (* Establish df_boundary fact BEFORE expanding invariant *)
  `case df_boundary NONE st lbl of NONE => T
   | SOME fmap => FDOM fmap SUBSET set (fn_all_assignments fn)`
    by metis_tac[df_boundary_inv] >>
  fs[copy_prop_state_inv_def] >>
  rpt conj_tac
  (* boundary *)
  >- (rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
      rw[] >> res_tac >>
      mp_tac (Q.SPECL [`df_boundary NONE st lbl`, `fv`, `set (fn_all_assignments fn)`]
                       copy_prop_join_fdom_subset) >>
      simp[] >> strip_tac >>
      Cases_on `copy_prop_join (df_boundary NONE st lbl) fv` >> gvs[])
  (* inst *)
  >- (rpt gen_tac >> simp[FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP inst_map k` >> simp[]
      >- (strip_tac >> res_tac)
      >- (strip_tac >> gvs[] >>
          first_x_assum (qspecl_then [`k`, `SOME fmap`] mp_tac) >> simp[]))
QED

(* measure_inv for initial state — C3,C4,C5 vacuously true since ds_inst=FEMPTY *)
Triviality copy_prop_measure_inv_initial[local]:
  !fn.
    fn_inst_wf fn ==>
    case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
      NONE => copy_prop_measure_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks))
    | SOME (lbl,v) => copy_prop_measure_inv fn
        (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
         ds_boundary :=
           (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary
             |+ (lbl,v))
Proof
  rpt strip_tac >>
  simp[copy_prop_measure_inv_def, init_df_state_def, LET_THM] >>
  mp_tac (SPEC_ALL copy_prop_init_state_inv) >>
  Cases_on `fn_entry_label fn` >> simp[init_df_state_def]
QED

(* SUM(MAP f l) ≤ SUM(MAP g l) when f ≤ g pointwise on l *)
Triviality sum_map_le[local]:
  !f g l. EVERY (\x. f x <= g x) l ==> SUM (MAP f l) <= SUM (MAP g l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  irule LESS_EQ_LESS_EQ_MONO >> simp[]
QED

(* SUM(MAP f l) < SUM(MAP g l) when f ≤ g pointwise and strictly < at some MEM *)
Triviality sum_map_lt[local]:
  !f g l. EVERY (\x. f x <= g x) l /\
          (?x. MEM x l /\ f x < g x) ==>
          SUM (MAP f l) < SUM (MAP g l)
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  `SUM (MAP f l) <= SUM (MAP g l)` by (irule sum_map_le >> simp[])
  >- (gvs[] >>
      irule LESS_EQ_LESS_TRANS >>
      qexists_tac `g h + SUM (MAP f l)` >> simp[])
  >- (irule LESS_LESS_EQ_TRANS >>
      qexists_tac `f h + SUM (MAP g l)` >>
      reverse conj_tac >- simp[] >>
      simp[LT_ADD_LCANCEL] >>
      first_x_assum irule >> simp[] >> metis_tac[])
QED

(* Monotonicity: processing a dfs_pre label either leaves state unchanged or
   increases measure. *)
(* Helper: FDOM f ⊆ s ⇒ DRESTRICT f s = f *)
Triviality drestrict_subset_id[local]:
  !f (s:'a -> bool). FDOM f SUBSET s ==> DRESTRICT f s = f
Proof
  rpt strip_tac >>
  simp[GSYM fmap_EQ_THM, FDOM_DRESTRICT, INTER_SUBSET_EQN] >>
  rpt strip_tac >> simp[DRESTRICT_DEF]
QED

(* copy_val_measure strict when join differs *)
Triviality copy_val_measure_join_strict[local]:
  !mv a b.
    (case a of NONE => T | SOME fmap => CARD (FDOM fmap) <= mv) /\
    (case b of NONE => T | SOME fmap => CARD (FDOM fmap) <= mv) /\
    copy_prop_join a b <> a ==>
    copy_val_measure mv a < copy_val_measure mv (copy_prop_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_prop_join_def, copy_val_measure_def, copy_prop_join_raw_def,
       FDOM_DRESTRICT] >>
  rpt strip_tac >>
  (* DRESTRICT x ag ≠ x ⇒ ¬(FDOM x ⊆ ag) ⇒ FDOM x ∩ ag ⊂ FDOM x *)
  qabbrev_tac `ag = {x'' | copy_agree x x' x''}` >>
  `~(FDOM x SUBSET ag)` by metis_tac[drestrict_subset_id] >>
  `FDOM x INTER ag PSUBSET FDOM x` by (
    fs[PSUBSET_DEF, INTER_SUBSET, SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  `CARD (FDOM x INTER ag) < CARD (FDOM x)` by
    (irule CARD_PSUBSET >> simp[FDOM_FINITE]) >>
  simp[LE_SUB_LCANCEL]
QED

(* Case A helper: boundary strictly increases at lbl *)
Triviality boundary_measure_strict[local]:
  !fn lbl st.
    copy_prop_measure_inv fn st /\
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    copy_val_measure (CARD (set (fn_all_assignments fn)))
                     (df_boundary NONE st lbl) <
    copy_val_measure (CARD (set (fn_all_assignments fn))) new_val ==>
    copy_boundary_measure fn st <
    copy_boundary_measure fn (st with ds_boundary := st.ds_boundary |+ (lbl, new_val))
Proof
  rpt strip_tac >>
  simp[copy_boundary_measure_def, LET_THM] >>
  ntac 2 (once_rewrite_tac[GSYM MAP_APPEND]) >>
  irule sum_map_lt >> simp[] >>
  `!x. copy_val_measure (CARD (set (fn_all_assignments fn)))
         (df_boundary NONE
            (st with ds_boundary := st.ds_boundary |+ (lbl, new_val)) x) =
       if x = lbl then
         copy_val_measure (CARD (set (fn_all_assignments fn))) new_val
       else
         copy_val_measure (CARD (set (fn_all_assignments fn)))
           (df_boundary NONE st x)` by
    (rpt strip_tac >> simp[df_boundary_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> simp[]) >>
  rpt conj_tac >>
  TRY (simp[EVERY_MEM] >> rpt strip_tac >>
       IF_CASES_TAC >> simp[] >> NO_TAC) >>
  qexists_tac `lbl` >> fs[MEM_APPEND]
QED

(* joined only depends on ds_boundary, not ds_inst *)
Triviality copy_prop_joined_inst_irrelevant[local]:
  !fn st X lbl.
    copy_prop_joined fn (st with ds_inst := X) lbl =
    copy_prop_joined fn st lbl
Proof
  simp[copy_prop_joined_def, LET_THM, df_boundary_def]
QED

(* Case B helper: fresh_count increases when v0 at lbl changes to joined *)
Triviality fresh_count_increase[local]:
  !fn st inst_map lbl.
    MEM lbl (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre) /\
    FLOOKUP inst_map (lbl, 0n) = SOME (copy_prop_joined fn st lbl) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    FLOOKUP (FUNION inst_map st.ds_inst) (lbl, 0n) <>
      FLOOKUP st.ds_inst (lbl, 0n) ==>
    copy_prop_fresh_count fn st <
    copy_prop_fresh_count fn (st with ds_inst := FUNION inst_map st.ds_inst)
Proof
  rpt strip_tac >>
  simp[copy_prop_fresh_count_def, LET_THM,
       copy_prop_joined_inst_irrelevant] >>
  irule CARD_PSUBSET >>
  simp[PSUBSET_MEMBER] >>
  conj_tac >- (
    irule SUBSET_FINITE >>
    qexists_tac `set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[SUBSET_DEF, MEM_APPEND]) >>
  conj_tac >- (
    simp[SUBSET_DEF, FDOM_FUNION, FLOOKUP_FUNION] >>
    rpt strip_tac >>
    Cases_on `FLOOKUP inst_map (x, 0n)` >> gvs[] >>
    `(x, 0n) IN FDOM inst_map` by fs[FLOOKUP_DEF] >>
    `FST (x, 0n:num) = lbl` by res_tac >> gvs[]) >>
  qexists_tac `lbl` >>
  conj_tac >- (
    gvs[FDOM_FUNION, FLOOKUP_FUNION, FLOOKUP_DEF, MEM_APPEND]) >>
  gvs[FLOOKUP_FUNION, FLOOKUP_DEF]
QED

(* Key properties of inst_map from df_fold_block *)
Triviality df_fold_block_inst_map_props[local]:
  !transfer lbl instrs v0 fv inst_map.
    df_fold_block Forward transfer lbl instrs v0 = (fv, inst_map) ==>
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    (lbl, 0n) IN FDOM inst_map /\
    FLOOKUP inst_map (lbl, 0n) = SOME v0
Proof
  rpt strip_tac >> imp_res_tac df_fold_block_fdom
  >- fs[IN_IMAGE, IN_COUNT]
  >- simp[IN_IMAGE, IN_COUNT]
  >- (qpat_x_assum `_ = (fv, inst_map)` mp_tac >>
      simp[dfAnalyzeDefsTheory.df_fold_block_def,
           dfAnalyzeDefsTheory.direction_case_def] >>
      strip_tac >> imp_res_tac df_fold_forward_at >> fs[])
QED

(* C3 coherence: when ds_inst already has the right v0 at (lbl,0),
   the fold output inst_map is absorbed by FUNION. *)
Triviality funion_fold_coherent[local]:
  !fn lbl st joined instrs fv inst_map.
    copy_prop_measure_inv fn st /\
    instrs = (case lookup_block lbl fn.fn_blocks of
                NONE => [] | SOME bb => bb.bb_instructions) /\
    df_fold_block Forward (copy_prop_transfer (phi_used_vars fn)) lbl
      instrs joined = (fv, inst_map) /\
    FLOOKUP st.ds_inst (lbl, 0n) = SOME joined ==>
    FUNION inst_map st.ds_inst = st.ds_inst
Proof
  rpt strip_tac >>
  (* Specialize C3 from measure_inv for our lbl/joined *)
  `!k v. FLOOKUP inst_map k = SOME v ==> FLOOKUP st.ds_inst k = SOME v` by (
    rpt strip_tac >>
    qpat_x_assum `copy_prop_measure_inv _ _` mp_tac >>
    simp_tac std_ss [copy_prop_measure_inv_def, LET_THM] >>
    strip_tac >>
    first_x_assum (qspecl_then [`lbl`, `joined`] mp_tac) >>
    impl_tac >- simp[] >>
    disch_then (qspecl_then [`k`, `v`] mp_tac) >>
    impl_tac >- (
      qpat_x_assum `instrs = _` (SUBST1_TAC o GSYM) >>
      qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th => simp[th])) >>
    simp[]) >>
  (* Now show FUNION absorption *)
  simp[fmap_eq_flookup] >> gen_tac >> simp[FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP inst_map x` >> simp[]
QED

Triviality ds_inst_update_literal[local]:
  !(st : 'a df_state) X.
    (st with ds_inst := X) = <|ds_inst := X; ds_boundary := st.ds_boundary|>
Proof
  simp[dfAnalyzeDefsTheory.df_state_component_equality]
QED

Triviality inst_card_mono[local]:
  !inst_map st fn.
    CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
    CARD (FDOM (FUNION inst_map st.ds_inst) INTER
          df_valid_inst_keys fn.fn_blocks)
Proof
  rpt strip_tac >>
  irule CARD_SUBSET >> simp[FINITE_INTER, FDOM_FUNION] >>
  simp[SUBSET_DEF, IN_INTER] >> metis_tac[IN_UNION]
QED

(* copy_prop_joined depends only on ds_boundary, and is preserved
   when df_boundary values are unchanged *)
Triviality copy_prop_joined_boundary_eq[local]:
  !fn st bnd di.
    (!x. df_boundary NONE <|ds_inst := di; ds_boundary := bnd|> x =
         df_boundary NONE st x) ==>
    !x. copy_prop_joined fn <|ds_inst := di; ds_boundary := bnd|> x =
        copy_prop_joined fn st x
Proof
  rpt strip_tac >>
  simp[copy_prop_joined_def, LET_THM]
QED

(* fresh_count monotonicity under FUNION when joined values are preserved *)
Triviality fresh_count_mono[local]:
  !fn st inst_map lbl bnd.
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    FLOOKUP inst_map (lbl, 0n) = SOME (copy_prop_joined fn st lbl) /\
    (!x. copy_prop_joined fn <|ds_inst := FUNION inst_map st.ds_inst;
                                ds_boundary := bnd|> x =
         copy_prop_joined fn st x) ==>
    copy_prop_fresh_count fn st <=
    copy_prop_fresh_count fn
      <|ds_inst := FUNION inst_map st.ds_inst; ds_boundary := bnd|>
Proof
  rpt strip_tac >>
  simp[copy_prop_fresh_count_def, LET_THM] >>
  irule CARD_SUBSET >>
  conj_tac >- (
    irule SUBSET_FINITE >>
    qexists_tac `set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` >>
    simp[SUBSET_DEF, MEM_APPEND]) >>
  simp[SUBSET_DEF, FDOM_FUNION, FLOOKUP_FUNION] >>
  rpt strip_tac >>
  TRY (simp[IN_UNION] >> NO_TAC) >>
  Cases_on `FLOOKUP inst_map (x, 0n)` >> simp[] >>
  `(x, 0n) IN FDOM inst_map` by fs[FLOOKUP_DEF] >>
  `FST (x, 0n:num) = lbl` by res_tac >> gvs[]
QED

Triviality fresh_count_bounded[local]:
  !fn st.
    copy_prop_fresh_count fn st <=
    LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  simp_tac std_ss [copy_prop_fresh_count_def, LET_THM] >>
  match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `CARD (set (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre))` >>
  conj_tac >- (
    irule CARD_SUBSET >> simp[FINITE_LIST_TO_SET, SUBSET_DEF]) >>
  match_mp_tac arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `LENGTH (fn_labels fn ++ (cfg_analyze fn).cfg_dfs_pre)` >>
  simp[CARD_LIST_TO_SET, LENGTH_APPEND]
QED

Triviality fold_output_card_bound[local]:
  !fn st lbl instrs joined fv inst_map.
    fn_inst_wf fn /\
    copy_prop_state_inv fn st /\
    instrs = (case lookup_block lbl fn.fn_blocks of
                NONE => [] | SOME bb => bb.bb_instructions) /\
    joined = copy_prop_joined fn st lbl /\
    df_fold_block Forward (copy_prop_transfer (phi_used_vars fn))
      lbl instrs joined = (fv, inst_map) ==>
    (case fv of NONE => T
     | SOME fmap => CARD (FDOM fmap) <= CARD (set (fn_all_assignments fn)))
Proof
  rpt strip_tac >>
  Cases_on `fv` >> simp[] >>
  `FDOM x SUBSET set (fn_all_assignments fn)` suffices_by
    metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET] >>
  drule copy_prop_fold_fdom >>
  disch_then (qspec_then `set (fn_all_assignments fn)` mp_tac) >>
  simp[] >>
  impl_tac >- (
    ASM_REWRITE_TAC [] >>
    conj_tac >- metis_tac[copy_prop_joined_inv] >>
    ASM_REWRITE_TAC [] >>
    metis_tac[copy_prop_transfer_preserves_fdom]) >>
  simp[]
QED

Triviality boundary_card_bound[local]:
  !fn st lbl.
    copy_prop_state_inv fn st ==>
    (case df_boundary NONE st lbl of NONE => T
     | SOME fmap => CARD (FDOM fmap) <= CARD (set (fn_all_assignments fn)))
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> simp[df_boundary_def] >>
  Cases_on `x` >> simp[] >>
  fs[copy_prop_state_inv_def] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[CARD_SUBSET, FINITE_LIST_TO_SET]
QED

Triviality weighted_lt_cancel[local]:
  !w (a:num) a' c. a < a' /\ c <= w ==> (w + 1) * a + c < (w + 1) * a'
Proof
  rpt strip_tac >>
  `(w + 1) * a + c <= (w + 1) * a + w` by simp[] >>
  `(w + 1) * a + w < (w + 1) * (a + 1)` by simp[LEFT_ADD_DISTRIB] >>
  `a + 1 <= a'` by simp[] >>
  `(w + 1) * (a + 1) <= (w + 1) * a'` by simp[LE_MULT_LCANCEL] >>
  simp[]
QED

Triviality copy_prop_measure_monotone[local]:
  !fn lbl st.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    copy_prop_measure_inv fn st /\
    df_process_block Forward NONE copy_prop_join copy_prop_transfer
      copy_prop_edge_transfer (phi_used_vars fn)
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st <> st ==>
    copy_prop_measure fn st <
    copy_prop_measure fn
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  rewrite_tac[copy_prop_process_eq] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  qabbrev_tac `joined = copy_prop_joined fn st lbl` >>
  qabbrev_tac `instrs = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions` >>
  qabbrev_tac `new_bnd = copy_prop_join (df_boundary NONE st lbl) fv` >>
  `(!k. k IN FDOM inst_map ==> FST k = lbl) /\
   (lbl, 0n) IN FDOM inst_map /\
   FLOOKUP inst_map (lbl, 0n) = SOME joined` by (
    qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th =>
      strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
    fs[Abbr `joined`]) >>
  `df_process_block Forward NONE copy_prop_join copy_prop_transfer
     copy_prop_edge_transfer (phi_used_vars fn)
     (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
     (cfg_analyze fn) fn.fn_blocks lbl st =
   st with <|ds_inst := FUNION inst_map st.ds_inst;
             ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|>` by (
    rewrite_tac[copy_prop_process_eq] >>
    simp_tac std_ss [LET_THM, Abbr `instrs`, Abbr `joined`, Abbr `new_bnd`] >>
    qpat_x_assum `df_fold_block _ _ _ _ _ = _` (fn th =>
      simp[th])) >>
  (* === Case split: did boundary value at lbl change? === *)
  Cases_on `df_boundary NONE st lbl = new_bnd`
  >- ( (* Case B: boundary unchanged *)
    Cases_on `lbl IN FDOM st.ds_boundary`
    >- ( (* B1: lbl IN FDOM, boundary unchanged *)
      `st.ds_boundary ' lbl = new_bnd` by (
        qpat_x_assum `df_boundary NONE st lbl = new_bnd` mp_tac >>
        simp[df_boundary_def, FLOOKUP_DEF]) >>
      `st.ds_boundary |+ (lbl, new_bnd) = st.ds_boundary` by
        (irule FUPDATE_ELIM >> metis_tac[]) >>
      simp_tac std_ss [copy_prop_measure_def, LET_THM] >>
      `copy_boundary_measure fn
         <|ds_inst := FUNION inst_map st.ds_inst;
           ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> =
       copy_boundary_measure fn st` by
        simp[copy_boundary_measure_def, LET_THM, df_boundary_def,
             FLOOKUP_UPDATE] >>
      `CARD (FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
             set (cfg_analyze fn).cfg_dfs_pre) =
       CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre)` by
        asm_rewrite_tac[] >>
      `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
       CARD (FDOM (FUNION inst_map st.ds_inst) INTER
             df_valid_inst_keys fn.fn_blocks)` by
        metis_tac[inst_card_mono] >>
      simp[] >>
      Cases_on `FLOOKUP st.ds_inst (lbl, 0n) = SOME joined`
      >- ( (* B1-YES: FUNION absorbed -> contradiction *)
        mp_tac (Q.SPECL [`fn`, `lbl`, `st`, `joined`,
          `instrs`, `fv`, `inst_map`] funion_fold_coherent) >>
        impl_tac >- (
          qpat_x_assum `Abbrev (instrs = _)` (mp_tac o
            REWRITE_RULE [markerTheory.Abbrev_def]) >>
          strip_tac >> simp[]) >>
        strip_tac >>
        qpat_x_assum `FUNION inst_map st.ds_inst = st.ds_inst` (fn funion_th =>
          qpat_x_assum `st.ds_boundary |+ _ = st.ds_boundary` (fn fupd_th =>
            qpat_x_assum `df_process_block _ _ _ _ _ _ _ _ _ _ st = _`
              (fn dpb_th => assume_tac
                (REWRITE_RULE [funion_th, fupd_th] dpb_th)))) >>
        gvs[df_state_component_equality]
      )
      >- ( (* B1-NO: fresh_count strictly increases *)
        mp_tac fresh_count_increase >>
        disch_then (qspecl_then [`fn`, `st`, `inst_map`, `lbl`] mp_tac) >>
        impl_tac >- (
          conj_tac >- simp[MEM_APPEND] >>
          conj_tac >- (
            qpat_x_assum `Abbrev (joined = _)` (mp_tac o
              REWRITE_RULE [markerTheory.Abbrev_def]) >>
            strip_tac >> ASM_REWRITE_TAC []) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          simp[FLOOKUP_FUNION]) >>
        disch_then (assume_tac o ONCE_REWRITE_RULE [ds_inst_update_literal]) >>
        gvs[] >> DECIDE_TAC
      ) (* end B1-NO *)
    ) (* end B1 *)
    >- ( (* B2: lbl NOT in boundary, boundary value unchanged *)
      `new_bnd = NONE` by (
        fs[df_boundary_def] >>
        Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[FLOOKUP_DEF]) >>
      simp_tac std_ss [copy_prop_measure_def, LET_THM] >>
      `copy_boundary_measure fn
         <|ds_inst := FUNION inst_map st.ds_inst;
           ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> =
       copy_boundary_measure fn st` by (
        rw[copy_boundary_measure_def] >>
        AP_TERM_TAC >> ONCE_REWRITE_TAC [GSYM MAP_APPEND] >>
        simp[MAP_EQ_f, df_boundary_def, FLOOKUP_UPDATE] >>
        rw[] >> fs[FLOOKUP_DEF]) >>
      `CARD (FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
             set (cfg_analyze fn).cfg_dfs_pre) =
       CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) + 1` by (
        `FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
           set (cfg_analyze fn).cfg_dfs_pre =
         lbl INSERT (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre)` by (
          simp[EXTENSION, FDOM_FUPDATE, IN_INTER] >> metis_tac[]) >>
        simp[] >>
        `lbl NOTIN (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre)` by
          simp[IN_INTER] >>
        simp[CARD_INSERT, FINITE_INTER]) >>
      `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
       CARD (FDOM (FUNION inst_map st.ds_inst) INTER
             df_valid_inst_keys fn.fn_blocks)` by
        metis_tac[inst_card_mono] >>
      `copy_prop_fresh_count fn st <=
       copy_prop_fresh_count fn
         <|ds_inst := FUNION inst_map st.ds_inst;
           ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|>` by (
        mp_tac fresh_count_mono >>
        disch_then (qspecl_then [`fn`, `st`, `inst_map`, `lbl`,
          `st.ds_boundary |+ (lbl, new_bnd)`] mp_tac) >>
        impl_tac >- (
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- (
            qpat_x_assum `Abbrev (joined = _)` (mp_tac o
              REWRITE_RULE [markerTheory.Abbrev_def]) >>
            strip_tac >> ASM_REWRITE_TAC []) >>
          irule copy_prop_joined_boundary_eq >>
          simp[df_boundary_def, FLOOKUP_UPDATE] >>
          rw[] >> gvs[df_boundary_def, FLOOKUP_DEF]) >>
        simp[]) >>
      gvs[] >> DECIDE_TAC
    ) (* end B2 *)
  ) (* end Case B *)
  >- ( (* Case A: boundary strictly changed *)
    `case fv of NONE => T
     | SOME fmap => CARD (FDOM fmap) <=
                    CARD (set (fn_all_assignments fn))` by (
      mp_tac fold_output_card_bound >>
      disch_then (qspecl_then [`fn`, `st`, `lbl`, `instrs`, `joined`,
        `fv`, `inst_map`] mp_tac) >>
      impl_tac >- (
        qpat_x_assum `copy_prop_measure_inv _ _` mp_tac >>
        simp_tac std_ss [copy_prop_measure_inv_def] >> strip_tac >>
        qpat_x_assum `Abbrev (joined = _)` (mp_tac o
          REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_x_assum `Abbrev (instrs = _)` (mp_tac o
          REWRITE_RULE [markerTheory.Abbrev_def]) >>
        rpt strip_tac >> ASM_REWRITE_TAC []) >>
      simp[]) >>
    `case df_boundary NONE st lbl of NONE => T
     | SOME fmap => CARD (FDOM fmap) <=
                    CARD (set (fn_all_assignments fn))` by (
      irule boundary_card_bound >>
      fs[copy_prop_measure_inv_def]) >>
    simp_tac std_ss [copy_prop_measure_def, LET_THM] >>
    `copy_boundary_measure fn st <
     copy_boundary_measure fn
       (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))` by (
      irule boundary_measure_strict >> simp[MEM_APPEND] >>
      qpat_x_assum `Abbrev (new_bnd = _)` (SUBST_ALL_TAC o
        REWRITE_RULE [markerTheory.Abbrev_def]) >>
      irule copy_val_measure_join_strict >> simp[]) >>
    `copy_boundary_measure fn
       <|ds_inst := FUNION inst_map st.ds_inst;
         ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> =
     copy_boundary_measure fn
       (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))` by
      simp[copy_boundary_measure_def, LET_THM, df_boundary_def] >>
    `CARD (FDOM st.ds_inst INTER df_valid_inst_keys fn.fn_blocks) <=
     CARD (FDOM (FUNION inst_map st.ds_inst) INTER
           df_valid_inst_keys fn.fn_blocks)` by
      metis_tac[inst_card_mono] >>
    `CARD (FDOM st.ds_boundary INTER set (cfg_analyze fn).cfg_dfs_pre) <=
     CARD (FDOM (st.ds_boundary |+ (lbl, new_bnd)) INTER
           set (cfg_analyze fn).cfg_dfs_pre)` by (
      irule CARD_SUBSET >> simp[FINITE_INTER, FDOM_FUPDATE] >>
      simp[SUBSET_DEF, IN_INTER] >> metis_tac[IN_INSERT]) >>
    assume_tac (Q.SPECL [`fn`, `st`] fresh_count_bounded) >>
    gvs[] >>
    mp_tac (ISPECL [
      ``LENGTH (fn_labels fn) + LENGTH (cfg_analyze fn).cfg_dfs_pre``,
      ``copy_boundary_measure fn st``,
      ``copy_boundary_measure fn
          (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd))``,
      ``copy_prop_fresh_count fn st``] weighted_lt_cancel) >>
    simp[] >> DECIDE_TAC
  ) (* end Case A *)
QED

(* measure_inv is preserved by processing *)
Triviality copy_prop_measure_inv_preserved[local]:
  !fn lbl st.
    copy_prop_measure_inv fn st ==>
    copy_prop_measure_inv fn
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks lbl st)
Proof
  rpt strip_tac >>
  simp[copy_prop_measure_inv_def] >>
  conj_tac >- fs[copy_prop_measure_inv_def] >>
  conj_tac >- (
    irule copy_prop_inv_preserved >>
    fs[copy_prop_measure_inv_def]) >>
  simp[copy_prop_process_eq, LET_THM] >>
  simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  fs[copy_prop_measure_inv_def, LET_THM] >>
  qabbrev_tac `instrs = case lookup_block lbl fn.fn_blocks of
                           NONE => [] | SOME bb => bb.bb_instructions` >>
  qabbrev_tac `joined = copy_prop_joined fn st lbl` >>
  rpt conj_tac
  (* C3: fold coherence — all inst_map keys have FST=lbl *)
  >- (rpt strip_tac >>
      qunabbrev_tac `instrs` >>
      qpat_x_assum `df_fold_block _ _ lbl _ joined = _`
        (fn th => assume_tac th >>
                  strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
      Cases_on `lbl' = lbl`
      >- ((* lbl'=lbl: v0=joined, fold=inst_map *)
        `v0 = joined` by
          (fs[FLOOKUP_FUNION]) >>
        fs[] >>
        simp[FLOOKUP_FUNION])
      >- ((* lbl'≠lbl *)
        `(lbl', 0n) NOTIN FDOM inst_map` by
          (strip_tac >> `FST (lbl', 0n) = lbl` by metis_tac[] >> fs[]) >>
        `FLOOKUP st.ds_inst (lbl', 0n) = SOME v0` by
          fs[FLOOKUP_FUNION, FLOOKUP_DEF] >>
        `FLOOKUP st.ds_inst k = SOME v` by metis_tac[] >>
        `k NOTIN FDOM inst_map` suffices_by
          (strip_tac >> simp[FLOOKUP_FUNION, FLOOKUP_DEF]) >>
        strip_tac >>
        `FST k = lbl` by metis_tac[] >>
        Cases_on `df_fold_block Forward (copy_prop_transfer (phi_used_vars fn))
                    lbl' (case lookup_block lbl' fn.fn_blocks of
                            NONE => [] | SOME bb => bb.bb_instructions) v0` >>
        qpat_x_assum `df_fold_block _ _ lbl' _ _ = (q, r)` (fn th =>
          strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
        fs[] >>
        `FST k = lbl'` by metis_tac[flookup_thm] >>
        fs[]))
  (* C4: key closure — (lbl',j) ∈ FDOM(inst_map ⊌ ds_inst) ⇒ (lbl',0) ∈ ... *)
  >- (rpt strip_tac >>
      qpat_x_assum `df_fold_block _ _ lbl _ _ = _` (fn th =>
        strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
      fs[FDOM_FUNION] >>
      res_tac >> fs[])
  (* C5: processed implies boundary exists *)
  >- (rpt strip_tac >>
      qpat_x_assum `df_fold_block _ _ lbl _ _ = _` (fn th =>
        strip_assume_tac (MATCH_MP df_fold_block_inst_map_props th)) >>
      fs[FDOM_FUNION, FDOM_FUPDATE] >>
      res_tac >> fs[])
QED

(* ===== Copy-prop specific: function-level simulation ===== *)

(* Forward-specialized fixpoint/transfer theorems *)
val fixpoint_restricted_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_process_restricted));
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_intra_transfer_proof));
val boundary_fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_boundary_fixpoint_proof));

(* copy_prop_join from right preserves soundness when b <> NONE *)
Theorem copy_sound_join_right[local]:
  !a b s. copy_sound_opt b s /\ b <> NONE ==>
          copy_sound_opt (copy_prop_join a b) s
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_sound_opt_def, copy_prop_join_def] >>
  rpt strip_tac >>
  rename1 `copy_sound (copy_prop_join_raw m1 m2) s` >>
  fs[copy_sound_def, copy_prop_join_raw_def] >>
  rpt strip_tac >>
  fs[FLOOKUP_DRESTRICT, copy_agree_def] >>
  Cases_on `FLOOKUP m2 x` >> gvs[]
QED

Theorem copy_sound_join_left[local]:
  !a b s. copy_sound_opt a s /\ a <> NONE ==>
          copy_sound_opt (copy_prop_join a b) s
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_sound_opt_def, copy_prop_join_def] >>
  rpt strip_tac >>
  rename1 `copy_sound (copy_prop_join_raw m1 m2) s` >>
  fs[copy_sound_def, copy_prop_join_raw_def] >>
  rpt strip_tac >>
  fs[FLOOKUP_DRESTRICT]
QED

Theorem foldl_join_sound_gen[local]:
  !vals acc v s.
    MEM v (acc :: vals) /\ v <> NONE /\ copy_sound_opt v s ==>
    copy_sound_opt (FOLDL copy_prop_join acc vals) s
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`copy_prop_join acc h`] mp_tac) >>
  disch_then irule
  >- (qexists_tac `copy_prop_join acc h` >> simp[] >>
      conj_tac
      >- (Cases_on `acc` >> Cases_on `h` >> fs[copy_prop_join_def])
      >- (irule copy_sound_join_left >> fs[]))
  >- (qexists_tac `copy_prop_join acc h` >> simp[] >>
      conj_tac
      >- (Cases_on `acc` >> Cases_on `h` >> fs[copy_prop_join_def])
      >- (irule copy_sound_join_right >> fs[]))
  >- (qexists_tac `v` >> fs[])
QED

Theorem foldl_join_sound[local]:
  !vals v s.
    MEM v vals /\ v <> NONE /\ copy_sound_opt v s ==>
    copy_sound_opt (FOLDL copy_prop_join NONE vals) s
Proof
  rpt strip_tac >>
  irule foldl_join_sound_gen >> metis_tac[MEM]
QED

(* cfg_analyze field accessor lemmas — avoids repeated pair destruct.
   Common tactic pattern: after simp[cfg_analyze_def, LET_THM], need
   Cases_on entry_block, Cases_on dfs_post_walk, Cases_on dfs_pre_walk *)
Triviality cfg_analyze_succs[local]:
  !fn. (cfg_analyze fn).cfg_succs = build_succs fn.fn_blocks
Proof
  simp[cfgDefsTheory.cfg_analyze_def, LET_THM] >>
  Cases_on `entry_block fn` >> simp[] >>
  Cases_on `dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label` >>
  Cases_on `dfs_pre_walk (build_succs fn.fn_blocks) [] x.bb_label` >>
  simp[]
QED

Triviality cfg_analyze_dfs_pre_none[local]:
  !fn. entry_block fn = NONE ==> (cfg_analyze fn).cfg_dfs_pre = []
Proof
  simp[cfgDefsTheory.cfg_analyze_def, LET_THM]
QED

Triviality cfg_analyze_dfs_pre_some[local]:
  !fn ebb. entry_block fn = SOME ebb ==>
    (cfg_analyze fn).cfg_dfs_pre =
      SND (dfs_pre_walk (build_succs fn.fn_blocks) [] ebb.bb_label)
Proof
  rpt strip_tac >>
  simp[cfgDefsTheory.cfg_analyze_def, LET_THM] >>
  Cases_on `dfs_post_walk (build_succs fn.fn_blocks) [] ebb.bb_label` >>
  Cases_on `dfs_pre_walk (build_succs fn.fn_blocks) [] ebb.bb_label` >>
  simp[]
QED

(* DFS pre-order closure: successors of reachable nodes are reachable *)
Triviality cfg_dfs_pre_succs_closed[local]:
  !fn lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    EVERY (\t. MEM t (cfg_analyze fn).cfg_dfs_pre)
      (cfg_succs_of (cfg_analyze fn) lbl)
Proof
  rpt strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  Cases_on `entry_block fn`
  >- (imp_res_tac cfg_analyze_dfs_pre_none >> fs[]) >>
  rename1 `entry_block fn = SOME ebb` >>
  imp_res_tac cfg_analyze_dfs_pre_some >> fs[cfgDefsTheory.cfg_succs_of_def] >>
  rw[cfg_analyze_succs] >>
  `MEM t (fmap_lookup_list (build_succs fn.fn_blocks) lbl)` by
    metis_tac[cfg_analyze_succs] >>
  imp_res_tac (CONJUNCT1 dfs_pre_walk_closure) >>
  `set (FST (dfs_pre_walk (build_succs fn.fn_blocks) [] ebb.bb_label)) =
   set (SND (dfs_pre_walk (build_succs fn.fn_blocks) [] ebb.bb_label))` by
    (mp_tac (CONJUNCT1 dfs_pre_walk_visited_eq |>
      ISPECL [``build_succs fn.fn_blocks``,
              ``[] : string list``, ``ebb.bb_label``]) >>
     simp[]) >>
  fs[EXTENSION]
QED

(* copy_sound_opt does not depend on vs_inst_idx *)
Theorem copy_sound_opt_inst_idx[local]:
  !v s k. copy_sound_opt v s <=> copy_sound_opt v (s with vs_inst_idx := k)
Proof
  Cases_on `v` >> rw[copy_sound_opt_def, copy_sound_def] >>
  eq_tac >> rpt strip_tac >> res_tac >>
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def]
QED

(* After run_block OK (non-halted), soundness transfers from entry to exit.
   Requires: no non-last instruction is a terminator. *)
Theorem run_block_exit_sound[local]:
  !(sound : 'a -> venom_state -> bool) (transfer : 'b -> instruction -> 'a -> 'a)
   run_ctx bottom result bb fuel ctx s s1.
    transfer_sound sound transfer run_ctx /\
    (!v s k. sound v s ==> sound v (s with vs_inst_idx := k)) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    sound (df_at bottom result bb.bb_label 0) s /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK s1 ==>
    sound (df_at bottom result bb.bb_label (LENGTH bb.bb_instructions)) s1
Proof
  rpt strip_tac >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx) s /\
     run_block fuel ctx bb s = OK s1 ==>
     sound (df_at bottom result bb.bb_label (LENGTH bb.bb_instructions)) s1`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    `i = LENGTH bb.bb_instructions` by fs[] >>
    qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode`
    >- (
      (* Terminator: must be last instruction *)
      `~(i < LENGTH bb.bb_instructions - 1)` by metis_tac[] >>
      `SUC i = LENGTH bb.bb_instructions` by fs[] >>
      Cases_on `v.vs_halted` >> gvs[] >>
      strip_tac >> gvs[] >>
      `df_at bottom result bb.bb_label (SUC i) =
       transfer run_ctx (EL i bb.bb_instructions)
         (df_at bottom result bb.bb_label i)` by
        (first_x_assum match_mp_tac >> fs[]) >>
      fs[transfer_sound_def] >>
      metis_tac[]
    )
    >- (
      (* Non-terminator: recurse with IH *)
      strip_tac >>
      `SUC i <= LENGTH bb.bb_instructions` by fs[] >>
      (* Apply IH *)
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[] >>
      disch_then match_mp_tac >>
      `df_at bottom result bb.bb_label (SUC i) =
       transfer run_ctx (EL i bb.bb_instructions)
         (df_at bottom result bb.bb_label i)` by res_tac >>
      `sound (transfer run_ctx (EL i bb.bb_instructions)
                (df_at bottom result bb.bb_label i)) v` by
        metis_tac[transfer_sound_def] >>
      metis_tac[]
    )
  )
QED

Theorem extract_labels_eq_map[local]:
  !ops lbls. EVERY (\op. IS_SOME (get_label op)) ops /\
    extract_labels ops = SOME lbls ==>
    MAP (THE o get_label) ops = lbls
Proof
  Induct >> rw[extract_labels_def] >>
  Cases_on `h` >> fs[get_label_def, extract_labels_def] >>
  Cases_on `extract_labels ops` >> fs[]
QED

(* After a well-formed terminator executes OK without halting,
   vs_current_bb is in get_successors of that instruction. *)
Theorem step_inst_base_term_succs[local]:
  !inst s s'.
    inst_wf inst /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\ ~s'.vs_halted ==>
    MEM s'.vs_current_bb (get_successors inst)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def] >>
  fs[step_inst_base_def, inst_wf_def, get_successors_def,
     get_label_def, AllCaseEqs(), jump_to_def, is_terminator_def] >>
  gvs[]
  (* JNZ cases: c is Var or Lit, so get_label c = NONE *)
  >- (Cases_on `c` >> fs[get_label_def])
  >- (Cases_on `c` >> fs[get_label_def])
  (* DJMP case *)
  >- (
    `MAP (THE o get_label) label_ops = labels` by
      metis_tac[extract_labels_eq_map] >>
    `FILTER IS_SOME (MAP get_label label_ops) = MAP get_label label_ops` by
      simp[FILTER_EQ_ID, EVERY_MAP] >>
    `MAP THE (MAP get_label label_ops) = labels` by
      fs[MAP_MAP_o] >>
    Cases_on `IS_SOME (get_label sel)` >> asm_rewrite_tac[MAP, MEM] >>
    fs[MEM_EL] >> metis_tac[MEM_EL])
QED

(* After run_block OK, vs_current_bb is in bb_succs bb *)
Theorem run_block_current_bb_in_succs[local]:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK s1 ==>
    MEM s1.vs_current_bb (bb_succs bb)
Proof
  rpt strip_tac >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     run_block fuel ctx bb s = OK s1 ==>
     MEM s1.vs_current_bb (bb_succs bb)`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      (* Terminator: must be last instruction *)
      Cases_on `v.vs_halted` >> gvs[] >>
      `~(i < LENGTH bb.bb_instructions - 1)` by metis_tac[] >>
      `i = PRE (LENGTH bb.bb_instructions)` by fs[] >> gvs[] >>
      `inst_wf (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions)` by
        (fs[EVERY_EL]) >>
      `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode
         <> INVOKE` by
        (CCONTR_TAC >> gvs[is_terminator_def]) >>
      `step_inst_base
         (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) s' = OK s1` by
        gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_succs >> strip_tac >>
      simp[bb_succs_def] >>
      Cases_on `bb.bb_instructions` >> gvs[LAST_EL, MEM_nub, MEM_REVERSE]
    )
    >- (
      (* Non-terminator: recurse with IH *)
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[]
    )
  )
QED

(* bb_succs of a member block are contained in cfg_succs_of *)
Theorem bb_succs_in_cfg_succs[local]:
  !fn bb lbl.
    ALL_DISTINCT (fn_labels fn) /\
    MEM bb fn.fn_blocks /\
    MEM lbl (bb_succs bb) ==>
    MEM lbl (cfg_succs_of (cfg_analyze fn) bb.bb_label)
Proof
  rpt strip_tac >>
  simp[cfgDefsTheory.cfg_succs_of_def, cfg_analyze_succs] >>
  `fmap_lookup_list (build_succs fn.fn_blocks) bb.bb_label = bb_succs bb` by (
    irule cfg_succs_of_build_succs >>
    fs[fn_labels_def]) >>
  fs[]
QED

(* Fixpoint property of copy_prop analysis *)
Triviality copy_prop_is_fixpoint[local]:
  !fn. fn_inst_wf fn ==>
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
Proof
  gen_tac >> strip_tac >>
  irule fixpoint_restricted_fwd >>
  conj_tac
  >- (match_mp_tac (SIMP_RULE std_ss [LET_THM]
        dfAnalyzeProofsTheory.df_process_deps_complete_proof |>
        SPEC ``Forward : direction`` |>
        SIMP_RULE std_ss [dfAnalyzeDefsTheory.direction_case_def]) >>
      rw[copy_prop_join_absorption] >>
      metis_tac[cfg_edge_symmetry])
  >>
  qexistsl_tac [
    `copy_prop_measure_inv fn`,
    `copy_prop_measure_bound fn`,
    `copy_prop_measure fn`,
    `\lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre`] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule copy_prop_measure_bounded >>
      fs[copy_prop_measure_inv_def])
  >- (rpt strip_tac >> fs[] >>
      metis_tac[copy_prop_measure_inv_preserved])
  >- (rpt strip_tac >> fs[] >>
      metis_tac[copy_prop_measure_monotone])
  >- (rpt strip_tac >> fs[] >>
      imp_res_tac cfg_dfs_pre_succs_closed >>
      fs[EVERY_MEM])
  >- simp[EVERY_MEM]
  >- (mp_tac (SPEC_ALL copy_prop_measure_inv_initial) >>
      Cases_on `fn_entry_label fn` >> simp[] >> metis_tac[])
QED

(* Remove is_fixpoint_def from srw_ss() — its expansion breaks
   imp_res_tac intra_fwd / boundary_fixpoint_fwd when is_fixpoint
   is an assumption. *)
val _ = delsimps ["is_fixpoint_def"];

Triviality run_block_ok_nonempty[local]:
  !fuel ctx bb s v. s.vs_inst_idx = 0 /\ run_block fuel ctx bb s = OK v ==>
    bb.bb_instructions <> []
Proof
  rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  `bb.bb_instructions = []` by fs[] >>
  qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
  simp[Once run_block_def, get_instruction_def]
QED

(* After running a block OK, the successor block is in cfg_dfs_pre *)
Triviality successor_in_cfg_dfs_pre[local]:
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
  rpt strip_tac >>
  `bb.bb_instructions <> []` by metis_tac[run_block_ok_nonempty] >>
  `EVERY inst_wf bb.bb_instructions` by (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `MEM v.vs_current_bb (bb_succs bb)` by metis_tac[run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[bb_succs_in_cfg_succs] >>
  imp_res_tac cfg_dfs_pre_succs_closed >> fs[EVERY_MEM]
QED

(* MEM + ALL_DISTINCT labels ==> lookup_block finds the block *)
Triviality MEM_lookup_block[local]:
  !lbl bbs (bb:basic_block).
    MEM bb bbs /\ bb.bb_label = lbl /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[MEM_MAP] >> rw[] >> gvs[lookup_block_def]
QED

(* ===== Pre-instantiated dataflow theorems for copy_prop ===== *)
(* These eliminate the generic polymorphic parameters so drule/drule_all
   can match directly against copy_prop-specific assumptions. *)

Triviality copy_prop_intra_fwd[local]:
  !fn lbl bb idx.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions
    ==>
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl (SUC idx) =
    copy_prop_transfer (phi_used_vars fn) (EL idx bb.bb_instructions)
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        lbl idx)
Proof
  rpt strip_tac >> imp_res_tac intra_fwd >> simp_tac std_ss []
QED

Triviality copy_prop_boundary_fixpoint[local]:
  !fn lbl bb.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb
    ==>
    df_boundary NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl =
    copy_prop_join
      (df_boundary NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        lbl)
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        lbl (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >> imp_res_tac boundary_fixpoint_fwd >> first_assum ACCEPT_TAC
QED

(* copy_prop_inter_fwd_gen: like inter_fwd but doesn't require lookup_block.
   For Forward direction, df_at lbl 0 = joined regardless of block existence.
   Proof: at fixpoint, df_process_block writes (lbl,0) -> joined to ds_inst
   via df_fold_forward (even with empty instrs when lookup_block = NONE). *)
Triviality copy_prop_inter_fwd_gen[local]:
  !fn lbl.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
    ==>
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl 0 =
    copy_prop_joined fn
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl
Proof
  rpt strip_tac >>
  qabbrev_tac `result = df_analyze Forward NONE copy_prop_join copy_prop_transfer
    copy_prop_edge_transfer (phi_used_vars fn)
    (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn` >>
  (* At fixpoint, process lbl result = result *)
  fs[worklistDefsTheory.is_fixpoint_def] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  simp[dfAnalyzeDefsTheory.df_process_block_def,
       dfAnalyzeDefsTheory.df_joined_val_def] >>
  pairarg_tac >> simp[] >>
  strip_tac >>
  (* inst_map SUBMAP result.ds_inst *)
  `inst_map ⊌ result.ds_inst = result.ds_inst` by
    (qpat_x_assum `<|ds_inst := _; ds_boundary := _|> = result` mp_tac >>
     rw[dfAnalyzeDefsTheory.df_state_component_equality]) >>
  `inst_map ⊑ result.ds_inst` by
    metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION] >>
  (* Unfold df_fold_block, then use df_fold_forward_at *)
  fs[dfAnalyzeDefsTheory.df_fold_block_def] >>
  drule dfAnalyzeProofsTheory.df_fold_forward_at >> strip_tac >>
  `FLOOKUP result.ds_inst (lbl, 0) =
   FLOOKUP inst_map (lbl, 0)` by
    metis_tac[finite_mapTheory.SUBMAP_FLOOKUP_EQN] >>
  fs[dfAnalyzeDefsTheory.df_at_def] >>
  simp[copy_prop_joined_def, copy_prop_edge_transfer_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> gvs[]
QED

Triviality copy_prop_df_at_not_none[local]:
  !fn lbl bb.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> []
    ==>
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl (LENGTH bb.bb_instructions) <> NONE
Proof
  rpt strip_tac >>
  `SUC (LENGTH bb.bb_instructions - 1) <= LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  drule_all copy_prop_intra_fwd >> strip_tac >>
  `copy_prop_transfer (phi_used_vars fn)
     (EL (LENGTH bb.bb_instructions - 1) bb.bb_instructions)
     (df_at NONE
       (df_analyze Forward NONE copy_prop_join copy_prop_transfer
          copy_prop_edge_transfer (phi_used_vars fn)
          (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
       lbl (LENGTH bb.bb_instructions - 1)) <> NONE` by
    simp_tac std_ss [copy_prop_transfer_def, LET_THM] >>
  `SUC (LENGTH bb.bb_instructions - 1) = LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  metis_tac[]
QED

(* Pre-instantiated: entry soundness ==> exit soundness for copy_prop *)
Triviality copy_prop_exit_sound[local]:
  !fn bb fuel ctx s v.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    copy_sound_opt
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        bb.bb_label 0) s /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK v
    ==>
    copy_sound_opt
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        bb.bb_label (LENGTH bb.bb_instructions)) v
Proof
  rpt strip_tac >>
  match_mp_tac (INST_TYPE [beta |-> ``:(string -> bool)``] run_block_exit_sound) >>
  MAP_EVERY qexists_tac [`copy_prop_transfer`, `phi_used_vars fn`,
    `fuel`, `ctx`, `s`] >>
  rpt conj_tac
  >- metis_tac[copy_prop_transfer_sound]
  >- (rpt strip_tac >> metis_tac[copy_sound_opt_inst_idx])
  >- (rpt strip_tac >> imp_res_tac intra_fwd >> simp_tac std_ss [])
  >- metis_tac[]
  >- metis_tac[]
  >- first_assum ACCEPT_TAC
  >> first_assum ACCEPT_TAC
QED

(* If one predecessor boundary is sound/non-NONE, then copy_prop_joined is sound.
   Abstracts over the entry-label wrapping. *)
Triviality copy_prop_joined_sound_from_pred[local]:
  !fn result lbl v nbr.
    MEM nbr (cfg_preds_of (cfg_analyze fn) lbl) /\
    df_boundary NONE result nbr <> NONE /\
    copy_sound_opt (df_boundary NONE result nbr) v
    ==>
    copy_sound_opt (copy_prop_joined fn result lbl) v
Proof
  rpt strip_tac >>
  simp[copy_prop_joined_def, LET_THM] >>
  (* MEM nbr implies MAP is non-empty *)
  `MAP (\nbr. df_boundary NONE result nbr)
       (cfg_preds_of (cfg_analyze fn) lbl) <> []` by
    (strip_tac >> fs[MAP_EQ_NIL, MEM]) >>
  Cases_on `MAP (\nbr. df_boundary NONE result nbr)
                (cfg_preds_of (cfg_analyze fn) lbl)`
  >- fs[]
  >>
  simp[] >>
  (* Base = FOLDL NONE (h::t) is sound *)
  `MEM (df_boundary NONE result nbr) (h::t)` by (
    qpat_assum `MAP _ _ = _` (fn th => REWRITE_TAC [SYM th]) >>
    simp[MEM_MAP] >> qexists_tac `nbr` >> simp[]) >>
  `copy_sound_opt (FOLDL copy_prop_join NONE (h::t)) v` by
    metis_tac[foldl_join_sound] >>
  (* Entry wrapping preserves soundness *)
  Cases_on `fn_entry_label fn` >> gvs[] >>
  TRY (IF_CASES_TAC >> gvs[]) >>
  TRY (irule copy_prop_join_sound >> simp[copy_sound_opt_fempty])
QED

(* After running a block OK with entry soundness at fixpoint,
   the successor has entry soundness too *)
Triviality successor_entry_sound[local]:
  !fn bb fuel ctx s v.
    let pv = phi_used_vars fn in
    let ev = OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) in
    let result = df_analyze Forward NONE copy_prop_join
      copy_prop_transfer copy_prop_edge_transfer pv ev fn in
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer pv ev (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    copy_sound_opt (df_at NONE result s.vs_current_bb 0) s /\
    run_block fuel ctx bb s = OK v
    ==>
    copy_sound_opt (df_at NONE result v.vs_current_bb 0) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `bb.bb_instructions <> []` by metis_tac[run_block_ok_nonempty] >>
  `EVERY inst_wf bb.bb_instructions` by (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[GSYM fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by metis_tac[] >>
  (* Normalize: use bb.bb_label everywhere instead of s.vs_current_bb *)
  qpat_x_assum `bb.bb_label = s.vs_current_bb`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  (* Step 1: Exit soundness (entry → exit via intra-block transfer) *)
  drule_all copy_prop_exit_sound >> strip_tac >>
  (* Step 2: df_at exit <> NONE *)
  drule_all copy_prop_df_at_not_none >> strip_tac >>
  (* Step 3: Boundary fixpoint equation *)
  drule_all copy_prop_boundary_fixpoint >> strip_tac >>
  (* Step 4: Boundary soundness via join_right *)
  `copy_sound_opt (df_boundary NONE
     (df_analyze Forward NONE copy_prop_join copy_prop_transfer
        copy_prop_edge_transfer (phi_used_vars fn)
        (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
     bb.bb_label) v` by metis_tac[copy_sound_join_right] >>
  (* Step 5: Successor location *)
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[bb_succs_in_cfg_succs] >>
  `MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    (imp_res_tac cfg_dfs_pre_succs_closed >> gvs[EVERY_MEM]) >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) v.vs_current_bb)` by
    metis_tac[cfg_edge_symmetry] >>
  (* Step 6: Successor entry via inter-block transfer (no lookup_block needed) *)
  mp_tac (Q.SPECL [`fn`, `v.vs_current_bb`] copy_prop_inter_fwd_gen) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn inter_th => REWRITE_TAC [inter_th]) >>
  (* Step 6b: use helper — boundary <> NONE + sound implies joined is sound *)
  irule copy_prop_joined_sound_from_pred >>
  qexists_tac `bb.bb_label` >> rpt conj_tac
  >- ( (* df_boundary <> NONE: fixpoint boundary = join(boundary, exit), exit <> NONE *)
      strip_tac >>
      Cases_on `df_at NONE
         (df_analyze Forward NONE copy_prop_join copy_prop_transfer
            copy_prop_edge_transfer (phi_used_vars fn)
            (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
         bb.bb_label (LENGTH bb.bb_instructions)` >>
      gvs[copy_prop_join_def])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
QED

Triviality copy_prop_join_FEMPTY[local]:
  !x. copy_prop_join (SOME FEMPTY) x = SOME FEMPTY
Proof
  Cases >> simp[copy_prop_join_def, copy_prop_join_raw_def, DRESTRICT_FEMPTY]
QED

Triviality copy_sound_opt_at_entry[local]:
  fn_inst_wf fn /\
  fn_entry_label fn = SOME lbl
  ==>
  copy_sound_opt (df_at NONE (copy_prop_analyze fn) lbl 0) s
Proof
  rpt strip_tac >>
  (* Derive MEM lbl cfg_dfs_pre from fn_entry_label *)
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by (
    fs[fn_entry_label_def] >>
    Cases_on `entry_block fn` >> gvs[] >>
    drule cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first >>
    strip_tac >>
    metis_tac[rich_listTheory.HEAD_MEM]) >>
  drule copy_prop_is_fixpoint >> strip_tac >>
  mp_tac (Q.SPECL [`fn`, `lbl`] copy_prop_inter_fwd_gen) >>
  impl_tac >- simp[] >>
  disch_then (fn th =>
    simp_tac std_ss [copy_prop_analyze_def, LET_THM, th]) >>
  simp[copy_prop_joined_def, LET_THM] >>
  gvs[copy_prop_join_FEMPTY, copy_sound_opt_fempty]
QED

(* Phase 1 function-level: use df_analysis_pass_correct_sound framework *)
Theorem assign_subst_function_eq[local]:
  !fuel ctx fn s.
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    fn_inst_wf fn /\
    ALL_DISTINCT (fn_labels fn) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode)
    ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn_subst s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac
  (* Expand copy_prop_analyze in goal BEFORE adding framework *)
  \\ simp_tac std_ss [copy_prop_analyze_def, LET_THM]
  \\ mp_tac (ISPECL [
       ``state_equiv {} : venom_state -> venom_state -> bool``,
       ``execution_equiv {} : venom_state -> venom_state -> bool``,
       ``NONE : copy_lattice option``,
       ``copy_prop_join``,
       ``copy_prop_transfer``,
       ``copy_prop_edge_transfer : (string -> bool) -> string -> string ->
            copy_lattice option -> copy_lattice option``,
       ``phi_used_vars fn``,
       ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : copy_lattice)))
            (fn_entry_label fn)``,
       ``fn : ir_function``,
       ``copy_sound_opt``,
       ``\v inst. [assign_subst_inst v inst]``]
     (SIMP_RULE std_ss [LET_THM]
       analysisSimPropsTheory.df_analysis_pass_correct_sound))
  \\ impl_tac
  >- (rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel]
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      >- metis_tac[copy_prop_is_fixpoint]
      >- metis_tac[copy_prop_transfer_sound]
      >- (rpt strip_tac >>
          metis_tac[REWRITE_RULE [SIMP_RULE std_ss [LET_THM]
            copy_prop_analyze_def] copy_sound_opt_at_entry])
      >- (rpt strip_tac >> rpt conj_tac
          >- metis_tac[successor_in_cfg_dfs_pre]
          >- (mp_tac (SIMP_RULE std_ss [LET_THM] successor_entry_sound) >>
              disch_then irule >> rpt conj_tac >>
              TRY (first_assum ACCEPT_TAC) >>
              metis_tac[copy_prop_is_fixpoint]))
      >- metis_tac[assign_subst_inst_simulates]
      >- first_assum ACCEPT_TAC
      >- metis_tac[copy_sound_opt_state_equiv]
      >- (rpt strip_tac >>
          fs[state_equiv_def, execution_equiv_def, lookup_var_def]))
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  \\ simp[]
QED

(* ===== Combined: function-level correctness ===== *)

(* Monotonicity: lift_result for stronger relation implies lift_result for weaker *)
Theorem lift_result_weaken[local]:
  !R1_ok R2_ok R1_term R2_term r1 r2.
    (!s1 s2. R1_ok s1 s2 ==> R2_ok s1 s2) /\
    (!s1 s2. R1_term s1 s2 ==> R2_term s1 s2) /\
    lift_result R1_ok R1_term r1 r2 ==>
    lift_result R2_ok R2_term r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def]
QED

Theorem assign_elim_function_correct_proof:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    fn_inst_wf fn /\
    ALL_DISTINCT (fn_labels fn) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb inst x.
       MEM bb fn_subst.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN elim)
    ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assign_elim_function fn) s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  (* Phase 1: fn → fn_subst gives state_equiv {} (or fn errors) *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (ISPECL [``fuel:num``, ``ctx:ir_context``,
             ``fn:ir_function``, ``s:venom_state``]
     assign_subst_function_eq)) >>
  impl_tac >- simp[] >>
  strip_tac >- (
    (* Phase 1 gave Error — just forward it *)
    simp[]
  ) >>
  (* Have: lift_result state_equiv {} fn fn_subst *)
  (* Need: Error fn ∨ lift_result state_equiv elim fn (assign_elim_function fn) *)
  (* Apply Phase 2 *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (ISPECL [``fuel:num``, ``ctx:ir_context``,
             ``fn:ir_function``, ``s:venom_state``]
     assign_nop_dead_writes_correct)) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  (* Now: Phase 2 conclusion is disjunction about fn_subst → fn_elim *)
  strip_tac >- (
    (* Phase 2 gave Error on fn_subst *)
    Cases_on `run_function fuel ctx fn s` >>
    fs[lift_result_def]
  ) >>
  (* Have: Phase 1 lift_result (∅), Phase 2 lift_result (elim) *)
  (* Compose Phases 1+2+3 *)
  DISJ2_TAC >>
  (* Phase 3: clear_nops gives result_equiv {} *)
  qabbrev_tac `fn_elim = analysis_function_transform NONE
     (copy_prop_analyze fn)
     (\v inst. [assign_elim_inst (phi_used_vars fn) v inst]) fn` >>
  `assign_elim_function fn = clear_nops_function fn_elim` by
    simp[assign_elim_function_def, Abbr `fn_elim`] >>
  `result_equiv {}
     (run_function fuel ctx fn_elim s)
     (run_function fuel ctx (assign_elim_function fn) s)` by (
    pop_assum (fn th => REWRITE_TAC [th]) >>
    irule clear_nops_function_correct >> simp[]) >>
  fs[result_equiv_is_lift_result] >>
  (* Weaken Phase 1 from state_equiv {} to state_equiv elim *)
  `lift_result (state_equiv (assign_elim_eliminated_vars fn))
     (execution_equiv (assign_elim_eliminated_vars fn))
     (run_function fuel ctx fn s)
     (run_function fuel ctx
        (analysis_function_transform NONE (copy_prop_analyze fn)
           (\v inst. [assign_subst_inst v inst]) fn) s)` by (
    irule lift_result_weaken >>
    qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
    simp[] >> rpt strip_tac >>
    metis_tac[state_equiv_subset, execution_equiv_subset, EMPTY_SUBSET]
  ) >>
  (* Compose Phases 1+2 via lift_result_trans *)
  `lift_result (state_equiv (assign_elim_eliminated_vars fn))
     (execution_equiv (assign_elim_eliminated_vars fn))
     (run_function fuel ctx fn s)
     (run_function fuel ctx fn_elim s)` by (
    irule lift_result_trans >>
    conj_tac >- (rpt strip_tac >> metis_tac[state_equiv_trans]) >>
    conj_tac >- (rpt strip_tac >> metis_tac[execution_equiv_trans]) >>
    qexists_tac `run_function fuel ctx
      (analysis_function_transform NONE (copy_prop_analyze fn)
         (\v inst. [assign_subst_inst v inst]) fn) s` >>
    simp[]) >>
  (* Compose with Phase 3 (clear_nops) *)
  irule lift_result_trans >>
  conj_tac >- (rpt strip_tac >> metis_tac[state_equiv_trans]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[execution_equiv_trans]) >>
  qexists_tac `run_function fuel ctx fn_elim s` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule lift_result_weaken >>
  qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
  simp[] >> rpt strip_tac >>
  metis_tac[state_equiv_subset, execution_equiv_subset, EMPTY_SUBSET]
QED
