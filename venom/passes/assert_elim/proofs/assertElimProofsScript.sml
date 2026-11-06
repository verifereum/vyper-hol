(*
 * Assert Elimination — Proofs
 *
 * 1. assert_elim_sim: per-instruction simulation
 * 2. assert_elim_function_correct_proof: function-level via range_pass_correct + clear_nops
 *)

Theory assertElimProofs
Ancestors
  analysisSimDefs
  analysisSimProps
  analysisSimProofsWiden
  assertElimDefs
  dfAnalyzeWidenDefs
  dfgAnalysisProps
  dfgSoundDefs
  dfgSoundProofs
  execEquivParamProps
  finite_map
  indexedLists
  list
  passSharedDefs
  passSharedProps
  passSimulationDefs
  passSimulationProps
  rangeAnalysisDefs
  rangeAnalysisProofs
  rangeEvalDefs
  rangeEvalProofs
  rangePassProofs
  stateEquiv
  stateEquivProps
  valueRangeDefs
  venomExecProofs
  venomExecProps
  venomExecSemantics
  venomInst
  venomInstProps
  venomState
  venomWf
  worklistDefs cfgCorrectnessProof dfAnalyzeWidenProofs
Libs
  pairLib


(* ===== Helper: range_excludes_zero + in_range ==> w <> 0w ===== *)

Theorem in_range_excludes_zero_nonzero[local]:
  !r w. in_range r w /\ range_excludes_zero r ==> w <> 0w
Proof
  Cases_on `r` >> simp[in_range_def, range_excludes_zero_def] >>
  rpt strip_tac >> gvs[] >>
  CCONTR_TAC >> gvs[integer_wordTheory.word_0_w2i] >>
  intLib.ARITH_TAC
QED

Theorem step_inst_assert_bad_arity[local]:
  !fuel ctx inst s.
    inst.inst_opcode = ASSERT ==>
    (inst.inst_operands = [] ==>
       step_inst fuel ctx inst s = Error "assert requires 1 operand") /\
    (!a b rest. inst.inst_operands = a::b::rest ==>
       step_inst fuel ctx inst s = Error "assert requires 1 operand")
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[step_inst_def] >>
  qpat_x_assum `inst.inst_opcode = ASSERT`
    (fn th => assume_tac th >> PURE_REWRITE_TAC[th]) >>
  simp[is_terminator_def] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = ASSERT`
    (fn th => PURE_REWRITE_TAC[th]) >>
  simp[]
QED

(* ===== Per-instruction simulation ===== *)

(* ASSERT transform preserves per-instruction behavior under range_sound *)
Theorem assert_elim_sim[local]:
  !v fuel ctx inst s.
    range_sound v s /\ inst_wf inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (step_inst fuel ctx inst s)
      (step_inst fuel ctx (assert_elim_inst v inst) s)
Proof
  rpt strip_tac >>
  reverse (Cases_on `inst.inst_opcode = ASSERT`)
  >- (simp[assert_elim_inst_def] >>
      metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl]) >>
  simp[assert_elim_inst_def] >>
  Cases_on `v`
  >- (simp[] >>
      metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl]) >>
  rename1 `SOME rs` >>
  Cases_on `inst.inst_operands`
  >- (DISJ1_TAC >> irule_at Any (cj 1 step_inst_assert_bad_arity) >> simp[]) >>
  reverse (Cases_on `t`)
  >- (DISJ1_TAC >> irule_at Any (cj 2 step_inst_assert_bad_arity) >> simp[]) >>
  Cases_on `h` >> simp[]
  (* Lit | Var | Label *)
  >- ((* Lit case *)
      rename1 `[Lit w]` >>
      reverse IF_CASES_TAC
      >- metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl] >>
      imp_res_tac step_inst_assert_1 >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      simp[eval_operand_def, mk_nop_inst_correct, lift_result_def, state_equiv_refl])
  >- ((* Var case *)
      rename1 `[Var var]` >>
      reverse IF_CASES_TAC
      >- metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl] >>
      fs[range_sound_def] >>
      imp_res_tac step_inst_assert_1 >>
      pop_assum (fn th => REWRITE_TAC [th]) >>
      simp[eval_operand_def, lookup_var_def, mk_nop_inst_correct] >>
      Cases_on `FLOOKUP s.vs_vars var` >> simp[lift_result_def, state_equiv_refl] >>
      rename1 `SOME w` >>
      imp_res_tac rs_lookup_in_range >>
      imp_res_tac in_range_excludes_zero_nonzero >>
      gvs[lift_result_def, state_equiv_refl])
  (* Label case: identity *)
  >> metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl]
QED

Theorem assert_elim_inst_structural[local]:
  inst_transform_structural_1 assert_elim_inst
Proof
  simp[inst_transform_structural_1_def] >> rpt conj_tac
  (* Terminators preserved *)
  >- (rpt strip_tac >> simp[assert_elim_inst_def] >>
      Cases_on `inst.inst_opcode` >> fs[is_terminator_def])
  (* INVOKE preserved *)
  >- (rpt strip_tac >> simp[assert_elim_inst_def])
  (* PHI preserved *)
  >- (rpt strip_tac >> simp[assert_elim_inst_def])
  (* Non-term non-INVOKE non-PHI preserved *)
  >- (rpt strip_tac >> gvs[assert_elim_inst_def] >>
      BasicProvers.every_case_tac >>
      gvs[mk_nop_inst_def, is_terminator_def])
QED

Theorem assert_elim_inst_cases[local]:
  !v inst. assert_elim_inst v inst = inst \/
           assert_elim_inst v inst = mk_nop_inst inst
Proof
  rpt gen_tac >> simp[assert_elim_inst_def] >>
  rpt (BasicProvers.PURE_CASE_TAC >> simp[])
QED

Theorem assert_elim_inst_id[local]:
  !v inst. (assert_elim_inst v inst).inst_id = inst.inst_id
Proof
  rpt gen_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

Theorem assert_elim_inst_outputs[local]:
  !v inst. (assert_elim_inst v inst).inst_outputs = inst.inst_outputs \/
           (assert_elim_inst v inst).inst_outputs = []
Proof
  rpt gen_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

Theorem assert_elim_inst_terminator[local]:
  !v inst. is_terminator inst.inst_opcode ==> assert_elim_inst v inst = inst
Proof
  rpt strip_tac >> simp[assert_elim_inst_def] >>
  IF_CASES_TAC >> simp[] >>
  fs[is_terminator_def]
QED

Theorem assert_elim_inst_not_terminator[local]:
  !v inst. ~is_terminator inst.inst_opcode ==>
           ~is_terminator (assert_elim_inst v inst).inst_opcode
Proof
  rpt gen_tac >> strip_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def, is_terminator_def]
QED

Theorem assert_elim_inst_phi[local]:
  !v inst. inst.inst_opcode = PHI ==>
           (assert_elim_inst v inst).inst_opcode = PHI
Proof
  rpt strip_tac >> simp[assert_elim_inst_def]
QED

Theorem assert_elim_inst_not_phi[local]:
  !v inst. inst.inst_opcode <> PHI ==>
           (assert_elim_inst v inst).inst_opcode <> PHI
Proof
  rpt gen_tac >> strip_tac >>
  DISJ_CASES_TAC (SPECL [``v : range_state option``, ``inst : instruction``]
                        assert_elim_inst_cases) >>
  simp[mk_nop_inst_def]
QED

Theorem assert_elim_analysis_transform_wf:
  !fn. wf_function fn ==>
       wf_function (analysis_function_transform_widen NONE (range_analyze fn)
         (\v inst. [assert_elim_inst v inst]) fn)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[aftw_singleton_eq_fmt_mapi] >>
  mp_tac (Q.SPECL
    [`\bb idx inst. assert_elim_inst
        (df_widen_at NONE (range_analyze fn) bb.bb_label idx) inst`,
     `fn`] passSimulationPropsTheory.mapi_transform_preserves_wf_bb) >>
  simp[assert_elim_inst_id, assert_elim_inst_terminator,
       assert_elim_inst_not_terminator, assert_elim_inst_phi,
       assert_elim_inst_not_phi]
QED

Theorem assert_elim_analysis_transform_ssa:
  !fn. wf_function fn /\ ssa_form fn ==>
       ssa_form (analysis_function_transform_widen NONE (range_analyze fn)
         (\v inst. [assert_elim_inst v inst]) fn)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[aftw_singleton_eq_fmt_mapi] >>
  mp_tac (Q.SPECL
    [`\bb idx inst. assert_elim_inst
        (df_widen_at NONE (range_analyze fn) bb.bb_label idx) inst`,
     `fn`] passSimulationPropsTheory.mapi_transform_preserves_ssa_bb) >>
  simp[assert_elim_inst_id, assert_elim_inst_outputs]
QED

(* Assert elimination preserves function-level semantics under range soundness.
   Eliminates provably-true assertions via range analysis, then clears NOPs. *)
Theorem assert_elim_function_correct_proof:
  !fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s.vs_vars) /\
    range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (assert_elim_function fn) s)
Proof
  rpt strip_tac >> simp[assert_elim_function_def] >>
  mp_tac (BETA_RULE (Q.SPECL [`fn`, `\bb idx t. T`, `assert_elim_inst`]
                       range_pass_correct)) >>
  impl_tac
  >- (REWRITE_TAC [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- ACCEPT_TAC assert_elim_inst_structural >>
      rpt strip_tac >>
      mp_tac (Q.SPECL [`df_widen_at NONE (range_analyze fn) bb.bb_label idx`,
        `fuel`, `ctx`, `EL idx bb.bb_instructions`, `t`] assert_elim_sim) >>
      impl_tac
      >- (conj_tac >- first_assum ACCEPT_TAC >>
          fs[fn_inst_wf_def] >> first_x_assum irule >> metis_tac[MEM_EL]) >>
      disch_then ACCEPT_TAC) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac
  >- (DISJ1_TAC >> metis_tac[]) >>
  DISJ2_TAC >>
  irule lift_result_trans >>
  conj_tac >- metis_tac[state_equiv_trans] >>
  conj_tac >- metis_tac[execution_equiv_trans] >>
  goal_assum drule >>
  simp_tac std_ss [GSYM result_equiv_is_lift_result] >>
  irule clear_nops_function_correct >>
  simp[assert_elim_analysis_transform_wf]
QED
