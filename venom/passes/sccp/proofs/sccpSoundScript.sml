(*
 * SCCP — Soundness and Per-Instruction Simulation
 *
 * Key results:
 *   const_sound_sccp_bottom      — FEMPTY is trivially sound
 *   const_sound_state_equiv      — preserved under state_equiv {}
 *   sccp_inst_step_correct       — sccp_inst preserves step_inst semantics
 *   sccp_inst_simulates          — wraps above for analysis framework
 *   sccp_transfer_sound          — sccp_transfer_inst preserves const_sound
 *)

Theory sccpSound
Ancestors
  sccpDefs analysisSimProps passSimulationProps venomWf venomInstProps
  cfgAnalysisProps passSharedProps
  venomState venomInst analysisSimDefs passSimulationDefs
  stateEquiv stateEquivProps execEquivParamDefs execEquivParamProps
  venomExecSemantics venomExecProofs passSharedDefs
  finite_map list pred_set dfAnalyzeDefs

(* ===== const_sound properties ===== *)

Theorem const_sound_sccp_bottom:
  !s. const_sound FEMPTY s
Proof
  simp[const_sound_def, FLOOKUP_DEF]
QED

Theorem const_sound_state_equiv:
  !st s1 s2. state_equiv {} s1 s2 /\ const_sound st s1 ==>
             const_sound st s2
Proof
  rpt strip_tac >>
  fs[const_sound_def, state_equiv_def, execution_equiv_def] >>
  rpt strip_tac >> res_tac >>
  `lookup_var v s1 = lookup_var v s2` by (first_x_assum irule >> simp[]) >>
  fs[lookup_var_def]
QED

Theorem const_sound_foldl_bottom[local]:
  !vars st s.
    const_sound st s ==>
    const_sound (FOLDL (\l v. l |+ (v, CL_Bottom)) st vars) s
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  fs[const_sound_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = h` >> gvs[]
QED

(* const_sound is only about vs_vars, not other fields *)
Theorem const_sound_update_var[local]:
  !st s v c.
    const_sound st s /\
    (!v' c'. v' <> v /\ FLOOKUP st v' = SOME (CL_Const c') ==>
             FLOOKUP s.vs_vars v' = SOME c') ==>
    const_sound (st |+ (v, CL_Const c))
      (s with vs_vars := s.vs_vars |+ (v, c))
Proof
  rw[const_sound_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v' = v` >> gvs[]
QED

(* After step_inst, non-output vars are preserved *)
Theorem foldl_bottom_preserves_const[local]:
  !outs st v c.
    FLOOKUP (FOLDL (\l v. l |+ (v, CL_Bottom)) st outs) v =
      SOME (CL_Const c) ==>
    ~MEM v outs /\ FLOOKUP st v = SOME (CL_Const c)
Proof
  Induct >- simp[] >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`st |+ (h, CL_Bottom)`, `v`, `c`] mp_tac) >>
  simp[] >> strip_tac >>
  `v <> h` by (CCONTR_TAC >> gvs[FLOOKUP_UPDATE]) >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem const_sound_after_step_bottom[local]:
  !st fuel ctx inst s s'.
    const_sound st s /\
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    const_sound (FOLDL (\l v. l |+ (v, CL_Bottom)) st
                  inst.inst_outputs) s'
Proof
  rpt strip_tac >> rw[const_sound_def] >> rpt strip_tac >>
  drule foldl_bottom_preserves_const >> strip_tac >>
  `lookup_var v s' = lookup_var v s` by
    metis_tac[step_preserves_non_output_vars] >>
  fs[const_sound_def, lookup_var_def]
QED

(* ===== const_subst_op correctness ===== *)

Theorem const_subst_op_correct:
  !st s op.
    const_sound st s ==>
    eval_operand (const_subst_op st op) s = eval_operand op s
Proof
  rpt strip_tac >>
  Cases_on `op` >>
  simp[const_subst_op_def, eval_operand_def, const_lookup_def] >>
  CASE_TAC >> simp[eval_operand_def, lookup_var_def] >>
  CASE_TAC >> simp[eval_operand_def, lookup_var_def] >>
  fs[const_sound_def, lookup_var_def]
QED

(* If const_subst_op maps an operand to a literal, that literal is its value *)
Theorem const_subst_op_lit[local]:
  !st s op c.
    const_sound st s /\ const_subst_op st op = Lit c ==>
    eval_operand op s = SOME c
Proof
  rpt strip_tac >>
  `eval_operand (const_subst_op st op) s = eval_operand op s`
    by metis_tac[const_subst_op_correct] >>
  gvs[eval_operand_def]
QED

(* ===== sccp_inst per-instruction correctness ===== *)

(* Helper: run_insts singleton *)
Theorem run_insts_sing[local]:
  !fuel ctx inst s.
    run_insts fuel ctx [inst] s = step_inst fuel ctx inst s
Proof
  rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[run_insts_def]
QED

(* Connection: const_subst_op = subst_op_map via FUN_FMAP *)
Triviality const_subst_fmap_finite[local]:
  !st:const_lattice.
    FINITE {v | ?c. FLOOKUP st v = SOME (CL_Const c)}
Proof
  gen_tac >> irule SUBSET_FINITE >>
  qexists_tac `FDOM st` >> simp[] >>
  rw[SUBSET_DEF] >> gvs[FLOOKUP_DEF]
QED

Triviality const_subst_as_subst_op_map[local]:
  !st op.
    subst_op_map
      (FUN_FMAP (\v. Lit (@c. FLOOKUP st v = SOME (CL_Const c)))
                {v | ?c. FLOOKUP st v = SOME (CL_Const c)}) op =
    const_subst_op st op
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[subst_op_map_def, const_subst_op_def, const_lookup_def] >>
  `FINITE {v | ?c. FLOOKUP st v = SOME (CL_Const c)}`
    by simp[const_subst_fmap_finite] >>
  simp[FLOOKUP_FUN_FMAP] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> gvs[] >>
  CASE_TAC >> gvs[]
QED

(* Operand-substituted instruction equals original via subst_operands_map *)
Theorem const_subst_step_eq[local]:
  !st fuel ctx inst s.
    const_sound st s /\ inst_wf inst /\ inst.inst_opcode <> PHI ==>
    step_inst fuel ctx
      (inst with inst_operands := MAP (const_subst_op st) inst.inst_operands)
      s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  qabbrev_tac `subs = FUN_FMAP
    (\v. Lit (@c. FLOOKUP st v = SOME (CL_Const c)))
    {v | ?c. FLOOKUP st v = SOME (CL_Const c)}` >>
  `MAP (const_subst_op st) inst.inst_operands =
   MAP (subst_op_map subs) inst.inst_operands` by
    simp[MAP_EQ_f, Abbr `subs`, const_subst_as_subst_op_map] >>
  `inst with inst_operands :=
     MAP (const_subst_op st) inst.inst_operands =
   subst_operands_map subs inst` by
    simp[subst_operands_map_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule subst_operands_map_correct >>
  simp[Abbr `subs`] >> rpt strip_tac >>
  `FINITE {v' | ?c. FLOOKUP st v' = SOME (CL_Const c)}`
    by simp[const_subst_fmap_finite] >>
  gvs[FLOOKUP_FUN_FMAP] >>
  fs[const_sound_def] >>
  `FLOOKUP s.vs_vars v = SOME (@c. FLOOKUP st v = SOME (CL_Const c))` by
    (first_x_assum irule >> SELECT_ELIM_TAC >> metis_tac[]) >>
  simp[eval_operand_def, lookup_var_def]
QED

(* JNZ constant folding: JMP to target equals JNZ with known condition *)
Theorem jnz_const_fold_correct[local]:
  !fuel ctx inst s cond t_lbl f_lbl.
    inst.inst_opcode = JNZ ==>
    step_inst fuel ctx
      (if cond <> 0w then
         inst with <|inst_opcode := JMP; inst_operands := [Label t_lbl]|>
       else
         inst with <|inst_opcode := JMP; inst_operands := [Label f_lbl]|>) s =
    step_inst fuel ctx
      (inst with inst_operands := [Lit cond; Label t_lbl; Label f_lbl]) s
Proof
  rpt strip_tac >>
  IF_CASES_TAC >> gvs[] >> (
    simp[step_inst_non_invoke] >>
    simp[Once step_inst_base_def, eval_operand_def] >>
    simp[Once step_inst_base_def, eval_operand_def])
QED

(* Main theorem: sccp_inst with sound lattice = original instruction *)
Theorem sccp_inst_step_correct:
  !st fuel ctx inst s.
    const_sound st s /\ inst_wf inst ==>
    step_inst fuel ctx (sccp_inst st inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >- simp[sccp_inst_def]
  >>
  drule_all const_subst_step_eq >> strip_tac >>
  simp[sccp_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = JNZ` >> gvs[]
  >- (
    CASE_TAC >> gvs[] >>
    CASE_TAC >> gvs[] >>
    CASE_TAC >> gvs[] >>
    CASE_TAC >> gvs[] >>
    CASE_TAC >> gvs[] >>
    TRY (CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >> NO_TAC) >>
    CASE_TAC >> gvs[] >>
    CASE_TAC >> gvs[] >>
    simp[jnz_const_fold_correct])
  >>
  Cases_on `inst.inst_opcode = ASSERT \/
            inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (
    gvs[] >>
    CASE_TAC >> gvs[] >>
    CASE_TAC >> gvs[] >>
    CASE_TAC >> gvs[] >>
    IF_CASES_TAC >> gvs[] >>
    simp[mk_nop_inst_def, step_nop_identity] >>
    gvs[step_inst_non_invoke] >>
    simp[Once step_inst_base_def] >>
    drule_all const_subst_op_lit >> gvs[])
  >>
  simp[]
QED

(* ===== inst_transform_structural ===== *)

Theorem sccp_inst_structural[local]:
  inst_transform_structural (\lat inst. [sccp_inst lat.sl_vals inst])
Proof
  rw[inst_transform_structural_def] >> rpt conj_tac >> rpt gen_tac >>
  rw[sccp_inst_def, LET_THM, mk_nop_inst_def] >> rpt strip_tac >> (
    TRY (fs[is_terminator_def] >> NO_TAC) >>
    TRY (
      `~is_terminator (mk_nop_inst inst).inst_opcode /\
       (mk_nop_inst inst).inst_opcode <> INVOKE` by EVAL_TAC >>
      fs[]) >>
    rpt (CASE_TAC >> gvs[is_terminator_def]) >>
    rpt (IF_CASES_TAC >> gvs[is_terminator_def]) >>
    (* Remaining ASSERT/ASSERT_UNREACHABLE goals: case expr in asms *)
    TRY (qpat_x_assum `is_terminator _` mp_tac) >>
    TRY (qpat_x_assum `_ = INVOKE` mp_tac) >>
    simp_tac (srw_ss()) [] >>
    CASE_TAC >> gvs[is_terminator_def] >>
    rpt (CASE_TAC >> gvs[is_terminator_def]))
QED

(* ===== analysis_inst_simulates ===== *)

Theorem sccp_inst_simulates:
  analysis_inst_simulates (state_equiv {}) (execution_equiv {})
    (\lat. const_sound lat.sl_vals)
    (\lat inst. [sccp_inst lat.sl_vals inst])
Proof
  simp[analysis_inst_simulates_def] >>
  conj_tac
  >- (rpt strip_tac >> simp[run_insts_sing] >>
      `step_inst fuel ctx (sccp_inst lat.sl_vals inst) s =
       step_inst fuel ctx inst s`
        by metis_tac[sccp_inst_step_correct] >>
      simp[] >>
      Cases_on `step_inst fuel ctx inst s` >>
      simp[lift_result_def, state_equiv_refl, execution_equiv_refl])
  >- ACCEPT_TAC sccp_inst_structural
QED

(* ===== Transfer soundness ===== *)

(* General single-output lattice update soundness *)
Theorem const_sound_single_output[local]:
  !st fuel ctx inst s s' out cv.
    const_sound st s /\
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_outputs = [out] /\
    (!c. cv = CL_Const c ==> FLOOKUP s'.vs_vars out = SOME c) ==>
    const_sound (st |+ (out, cv)) s'
Proof
  rpt strip_tac >> rw[const_sound_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = out` >> gvs[] >>
  `lookup_var v s' = lookup_var v s` by (
    irule step_preserves_non_output_vars >>
    qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[MEM]) >>
  fs[const_sound_def, lookup_var_def]
QED

(* Helper: const_eval_operand soundness *)
Theorem const_eval_operand_sound[local]:
  !st s op c.
    const_sound st s /\ const_eval_operand st op = CL_Const c ==>
    eval_operand op s = SOME c
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[const_eval_operand_def, const_lookup_def, eval_operand_def,
      lookup_var_def] >>
  pop_assum mp_tac >> CASE_TAC >> gvs[] >>
  fs[const_sound_def, lookup_var_def]
QED

(* Helper: const_sound preserved when only sl_targets changes *)
Theorem const_sound_targets_update[local]:
  !lat tgts s.
    const_sound lat.sl_vals s ==>
    const_sound (lat with sl_targets := tgts).sl_vals s
Proof
  simp[]
QED

(* Helper: terminators preserve const_sound *)
Theorem const_sound_after_terminator[local]:
  !lat fuel ctx inst s s'.
    const_sound lat.sl_vals s /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    const_sound lat.sl_vals s'
Proof
  rpt strip_tac >> fs[const_sound_def] >> rpt strip_tac >>
  `lookup_var v s' = lookup_var v s`
    by metis_tac[step_terminator_preserves_vars] >>
  fs[lookup_var_def]
QED

(* Helper: no-output instructions preserve const_sound *)
Theorem const_sound_no_outputs[local]:
  !st fuel ctx inst s s'.
    const_sound st s /\
    inst.inst_outputs = [] /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    const_sound st s'
Proof
  rpt strip_tac >> fs[const_sound_def] >> rpt strip_tac >>
  `lookup_var v s' = lookup_var v s` by (
    irule step_preserves_non_output_vars >> metis_tac[MEM]) >>
  fs[lookup_var_def]
QED

(* Helper: const_eval_ops soundness — operands evaluate to ws *)
Theorem const_eval_ops_sound[local]:
  !st ops ws s.
    const_sound st s /\ const_eval_ops st ops = EvalConsts ws ==>
    MAP (\op. eval_operand op s) ops = MAP SOME ws
Proof
  Induct_on `ops` >> simp[const_eval_ops_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `const_eval_operand st h` >> gvs[] >>
  Cases_on `const_eval_ops st ops` >> gvs[] >>
  `eval_operand h s = SOME c` by metis_tac[const_eval_operand_sound] >>
  simp[] >> first_x_assum irule >> metis_tac[]
QED

(* Helper: ASSIGN [op] [out] gives update_var *)
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

(* Bridge: exec_pureN with MAP-known operand values gives update_var *)
Theorem exec_pure1_map_result[local]:
  !f inst v out s s'.
    exec_pure1 f inst s = OK s' /\
    MAP (\op. eval_operand op s) inst.inst_operands = [SOME v] /\
    inst.inst_outputs = [out] ==>
    s' = update_var out (f v) s
Proof
  rpt gen_tac >> simp[exec_pure1_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> rw[]
QED

Theorem exec_pure2_map_result[local]:
  !f inst v1 v2 out s s'.
    exec_pure2 f inst s = OK s' /\
    MAP (\op. eval_operand op s) inst.inst_operands = [SOME v1; SOME v2] /\
    inst.inst_outputs = [out] ==>
    s' = update_var out (f v1 v2) s
Proof
  rpt gen_tac >> simp[exec_pure2_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> rw[]
QED

Theorem exec_pure3_map_result[local]:
  !f inst v1 v2 v3 out s s'.
    exec_pure3 f inst s = OK s' /\
    MAP (\op. eval_operand op s) inst.inst_operands =
      [SOME v1; SOME v2; SOME v3] /\
    inst.inst_outputs = [out] ==>
    s' = update_var out (f v1 v2 v3) s
Proof
  rpt gen_tac >> simp[exec_pure3_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> rw[]
QED

(* Bridge: foldable opcodes compute via exec_pureN, matching const_eval_arith.
   Split into pure1/pure2/pure3 batches to avoid step_inst_base_def timeout. *)
Theorem foldable_step_result[local]:
  !inst s s' ws c out.
    is_sccp_foldable inst.inst_opcode /\
    inst.inst_outputs = [out] /\
    MAP (\op. eval_operand op s) inst.inst_operands = MAP SOME ws /\
    const_eval_arith inst.inst_opcode ws = SOME c /\
    step_inst_base inst s = OK s' ==>
    s' = update_var out c s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_sccp_foldable_def] >> (
    (* Destructure ws from const_eval_arith *)
    Cases_on `ws` >> gvs[const_eval_arith_def] >>
    TRY (Cases_on `t` >> gvs[const_eval_arith_def]) >>
    TRY (Cases_on `t'` >> gvs[const_eval_arith_def]) >>
    (* step_inst_base: rewrite with opcode eq to get exec_pureN *)
    qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
    asm_rewrite_tac [Once step_inst_base_def] >> simp[] >> strip_tac >>
    (* Apply exec_pureN_map_result to close *)
    TRY (drule exec_pure1_map_result >> simp[] >> NO_TAC) >>
    TRY (drule exec_pure2_map_result >> simp[] >> NO_TAC) >>
    (* For 3-arg (ADDMOD/MULMOD): need one more Cases_on *)
    TRY (Cases_on `t` >> gvs[const_eval_arith_def] >>
         drule exec_pure3_map_result >> simp[] >> NO_TAC))
QED

(* Helper: const_try_fold soundness *)
Theorem const_try_fold_sound:
  !st s fuel ctx inst out c s'.
    const_sound st s /\
    const_try_fold inst.inst_opcode st inst.inst_operands = CL_Const c /\
    is_sccp_foldable inst.inst_opcode /\
    inst.inst_outputs = [out] /\
    step_inst fuel ctx inst s = OK s' ==>
    FLOOKUP s'.vs_vars out = SOME c
Proof
  rpt strip_tac >>
  fs[const_try_fold_def] >>
  Cases_on `const_eval_ops st inst.inst_operands` >> gvs[] >>
  Cases_on `const_eval_arith inst.inst_opcode l` >> gvs[] >>
  `MAP (\op. eval_operand op s) inst.inst_operands = MAP SOME l` by (
    irule const_eval_ops_sound >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by (
    Cases_on `inst.inst_opcode` >> gvs[is_sccp_foldable_def]) >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  drule_all foldable_step_result >> strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE]
QED

Theorem sccp_transfer_sound:
  !fn. transfer_sound (\lat. const_sound lat.sl_vals)
         sccp_transfer_inst fn
Proof
  rw[transfer_sound_def] >> rpt strip_tac >>
  simp[sccp_transfer_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  REWRITE_TAC [FOLDL] >>
  (* Terminator goals *)
  TRY (irule const_sound_after_terminator >> metis_tac[] >> NO_TAC) >>
  (* No-output goals *)
  TRY (irule const_sound_no_outputs >> metis_tac[] >> NO_TAC) >>
  (* FOLDL-bottom goals (direct) *)
  TRY (irule const_sound_after_step_bottom >>
       simp[is_terminator_def] >> metis_tac[] >> NO_TAC) >>
  (* Multi-output partially-evaluated FOLDL *)
  TRY (`const_sound (FOLDL (\l v. l |+ (v, CL_Bottom))
          lat.sl_vals inst.inst_outputs) s'`
         by (irule const_sound_after_step_bottom >>
             simp[is_terminator_def] >> metis_tac[]) >>
       gvs[] >> NO_TAC) >>
  (* Single-output CL_Bottom goals *)
  TRY (irule const_sound_single_output >> simp[] >>
       rpt strip_tac >> gvs[] >> NO_TAC) >>
  (* Remaining 2 goals: ASSIGN and foldable single-output.
     Both need const_sound_single_output, which requires proving the
     FLOOKUP obligation: if the lattice value is CL_Const c then
     FLOOKUP s'.vs_vars out = SOME c. *)
  irule const_sound_single_output >> simp[] >>
  rpt strip_tac >>
  (* Existential side-goals from const_sound_single_output *)
  TRY (qexistsl_tac [`run_ctx`, `fuel`, `inst`, `s`] >> simp[] >> NO_TAC) >>
  imp_res_tac step_assign_result >> gvs[update_var_def, FLOOKUP_UPDATE] >>
  (* Goal 1: val = c from eval_operand + const_eval_operand_sound *)
  TRY (imp_res_tac const_eval_operand_sound >> gvs[] >> NO_TAC) >>
  (* Goal 2: foldable FLOOKUP from const_try_fold_sound *)
  irule const_try_fold_sound >> metis_tac[]
QED

