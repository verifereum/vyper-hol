(*
 * Assign Elimination — Sound Predicate and Per-Instruction Proofs
 *
 * TOP-LEVEL: copy_sound_def, copy_sound_opt_def,
 *   assign_subst_step_correct, assign_nop_dead_writes_correct
 * EXPORTED: copy_prop_transfer_sound, copy_prop_join_sound,
 *   copy_sound_opt_fempty, assign_subst_inst_simulates,
 *   copy_sound_opt_state_equiv
 *)

Theory assignElimSound
Ancestors
  assignElimDefs analysisSimProps passSimulationProps venomWf
  passSharedProps venomInstProps

open assignElimDefsTheory passSharedDefsTheory passSharedPropsTheory
     venomStateTheory venomWfTheory venomInstPropsTheory
     analysisSimDefsTheory analysisSimPropsTheory
     passSimulationPropsTheory passSimulationDefsTheory
     stateEquivTheory stateEquivPropsTheory
     execEquivParamDefsTheory execEquivParamPropsTheory
     venomExecSemanticsTheory finite_mapTheory
     listTheory pred_setTheory venomInstTheory
     dfAnalyzeDefsTheory

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
    DISJ2_TAC >> irule passSimulationPropsTheory.lift_result_refl >>
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
  DISJ2_TAC >> irule passSimulationPropsTheory.lift_result_refl >>
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
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def] >>
  imp_res_tac venomExecPropsTheory.step_inst_preserves_labels_always >> fs[]
QED

(* Terminator OK preserves vars. JMP/JNZI/DJMP only modify
   vs_current_bb/vs_prev_bb/vs_inst_idx, not vs_vars. *)
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

Theorem copy_prop_transfer_sound:
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
      >- metis_tac[venomExecPropsTheory.step_terminator_preserves_vars]
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

Theorem copy_prop_join_sound:
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

Theorem copy_sound_opt_fempty:
  !s. copy_sound_opt (SOME FEMPTY) s
Proof
  simp[copy_sound_opt_def, copy_sound_def, FLOOKUP_DEF]
QED

(* Phase 1: substitution gives state_equiv {} at function level.
   Uses the analysis framework with R_ok = state_equiv {}, R_term = execution_equiv {}.
   (Can't use $= directly because valid_state_rel $= $= is false.) *)
(* Inst-level simulation for assign_subst_inst *)
Theorem assign_subst_inst_simulates:
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
Theorem copy_sound_opt_state_equiv:
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
