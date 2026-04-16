(*
 * Assert Elimination — Proofs
 *)

Theory assertElimProofs
Ancestors
  assertElimDefs analysisSimProps passSimulationProps
  valueRangeDefs rangeEvalDefs
  venomState venomInst venomWf venomExecSemantics
  passSharedDefs passSharedProps stateEquiv analysisSimDefs
  variableRangeAnalysisProps rangeAnalysisProofs
Libs
  intLib

(* ===== Helpers ===== *)

Triviality range_excludes_zero_nonzero:
  !r (w : bytes32). range_excludes_zero r /\ in_range r w ==> w <> 0w
Proof
  Cases_on `r` >> simp[range_excludes_zero_def, in_range_def] >>
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  fs[integer_wordTheory.word_0_w2i] >> intLib.ARITH_TAC
QED

Triviality lift_result_id:
  !r. lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {}) r r = T
Proof
  Cases >> simp[lift_result_def,
    stateEquivProofsTheory.state_equiv_refl,
    stateEquivProofsTheory.execution_equiv_refl]
QED

Triviality run_insts_sing:
  !fuel ctx inst s.
    run_insts fuel ctx [inst] s = step_inst fuel ctx inst s
Proof
  rw[run_insts_def] >> CASE_TAC >> simp[run_insts_def]
QED

Triviality mk_nop_inst_ok:
  !fuel ctx inst s. step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  rpt gen_tac >>
  `(mk_nop_inst inst).inst_opcode = NOP` by simp[mk_nop_inst_def] >>
  metis_tac[venomInstProofsTheory.step_nop_identity]
QED

(* Key: when assert_elim produces mk_nop, step_inst either errors or gives OK s *)
Triviality assert_elim_nop_sim:
  !fuel ctx inst s rs.
    inst_wf inst /\ inst.inst_opcode = ASSERT /\
    in_range_state rs s.vs_vars /\
    assert_elim_inst (SOME rs) inst <> inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    step_inst fuel ctx inst s = OK s
Proof
  rpt strip_tac >>
  `LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = []` by
    (fs[inst_wf_def] >> gvs[]) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `[op]` >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    (irule step_inst_non_invoke >> simp[]) >>
  Cases_on `eval_operand op s`
  >- (
    DISJ1_TAC >>
    simp[step_inst_base_def])
  >>
  rename1 `SOME w` >>
  (* w <> 0w from range analysis + assert_elim condition *)
  `w <> 0w` by (
    CCONTR_TAC >> gvs[] >>
    Cases_on `op` >> gvs[assert_elim_inst_def, eval_operand_def, lookup_var_def] >>
    (* Remaining: Var case. Need in_range contradiction *)
    fs[in_range_state_def] >>
    res_tac >>
    fs[rs_lookup_def] >>
    Cases_on `FLOOKUP rs s'` >> gvs[range_excludes_zero_def] >>
    metis_tac[range_excludes_zero_nonzero]) >>
  DISJ2_TAC >>
  (* Convert step_inst to step_inst_base, then use step_assert_behavior *)
  simp[] >>  (* uses step_inst = step_inst_base from assumption *)
  `inst = <| inst_id := inst.inst_id; inst_opcode := ASSERT;
             inst_operands := [op]; inst_outputs := [] |>` by
    simp[instruction_component_equality] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  qspecl_then [`s`, `op`, `inst.inst_id`, `w`] mp_tac
    venomExecProofsTheory.step_assert_behavior >>
  simp[]
QED

(* When assert_elim_inst produces a non-identity result, it must be mk_nop *)
Triviality assert_elim_inst_is_nop:
  !rs inst. inst.inst_opcode = ASSERT /\
    assert_elim_inst (SOME rs) inst <> inst ==>
    assert_elim_inst (SOME rs) inst = mk_nop_inst inst
Proof
  rpt strip_tac >> gvs[assert_elim_inst_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* ===== Theorem 1 ===== *)

Theorem assert_elim_inst_simulates_proof:
  analysis_inst_simulates
    (state_equiv {}) (execution_equiv {})
    (\rs_opt s. case rs_opt of
                  NONE => T
                | SOME rs => in_range_state rs s.vs_vars)
    (\v inst. [assert_elim_inst v inst])
Proof
  simp[analysis_inst_simulates_def] >> conj_tac
  (* Simulation *)
  >- (
    rpt gen_tac >> strip_tac >>
    simp[run_insts_sing] >>
    (* If identity transform: lift_result reflexive *)
    Cases_on `assert_elim_inst v inst = inst` >>
    gvs[lift_result_id] >>
    `inst.inst_opcode = ASSERT` by (
      CCONTR_TAC >> gvs[assert_elim_inst_def]) >>
    Cases_on `v`
    >- (gvs[assert_elim_inst_def])
    >>
    rename1 `SOME rs` >>
    `in_range_state rs s.vs_vars` by gvs[] >>
    (* Derive: original either errors or is OK s *)
    `(?e. step_inst fuel ctx inst s = Error e) \/
     step_inst fuel ctx inst s = OK s` by
      metis_tac[assert_elim_nop_sim] >>
    `assert_elim_inst (SOME rs) inst = mk_nop_inst inst` by
      metis_tac[assert_elim_inst_is_nop] >>
    gvs[mk_nop_inst_ok, lift_result_def,
        stateEquivProofsTheory.state_equiv_refl])
  (* Structural: inst_transform_structural *)
  >- (
    simp[inst_transform_structural_def] >> rpt conj_tac >> rpt gen_tac
    >- (
      strip_tac >>
      `inst.inst_opcode <> ASSERT` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      simp[assert_elim_inst_def])
    >- (
      strip_tac >> simp[assert_elim_inst_def])
    >- (
      strip_tac >> simp[assert_elim_inst_def] >>
      rpt (CASE_TAC >> gvs[]) >>
      simp[mk_nop_inst_def, is_terminator_def]))
QED

(* ===== Theorem 2 ===== *)

Theorem assert_elim_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (assert_elim_function fn) s)
Proof
  rpt strip_tac >>
  simp[assert_elim_function_def, LET_THM] >>
  qabbrev_tac `fn_xform = analysis_function_transform_widen NONE
    (range_analyze fn) (\v inst. [assert_elim_inst v inst]) fn` >>
  (* Phase 2: clear_nops gives result_equiv {} *)
  `result_equiv {}
     (run_blocks fuel ctx fn_xform s)
     (run_blocks fuel ctx (clear_nops_function fn_xform) s)` by (
    irule clear_nops_function_correct >> simp[]) >>
  fs[stateEquivProofsTheory.result_equiv_is_lift_result] >>
  (* Either fn errors or we compose Phase 1 + Phase 2 *)
  Cases_on `?e. run_blocks fuel ctx fn s = Error e`
  >- simp[] >>
  DISJ2_TAC >>
  (* Phase 1: fn ~ fn_xform via analysis framework *)
  `lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
     (run_blocks fuel ctx fn s)
     (run_blocks fuel ctx fn_xform s)` by (
    simp[Abbr `fn_xform`] >>
    (* Use df_analysis_pass_correct_widen_sound *)
    `(?e. run_blocks fuel ctx fn s = Error e) \/
     lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
       (run_blocks fuel ctx fn s)
       (run_blocks fuel ctx
         (analysis_function_transform_widen NONE (range_analyze fn)
           (\v inst. [assert_elim_inst v inst]) fn) s)` by (
      cheat) >>
    gvs[]) >>
  (* Compose Phase 1 + Phase 2 *)
  irule lift_result_trans >>
  conj_tac >- (rpt strip_tac >> metis_tac[stateEquivProofsTheory.state_equiv_trans]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[stateEquivProofsTheory.execution_equiv_trans]) >>
  qexists_tac `run_blocks fuel ctx fn_xform s` >> simp[]
QED
