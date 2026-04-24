(*
 * Assert Elimination — Proofs
 *
 * 1. assert_elim_inst_simulates_proof: per-instruction simulation
 * 2. assert_elim_function_correct_proof: function-level via framework + clear_nops
 *)

Theory assertElimProofs
Ancestors
  analysisSimDefs
  analysisSimProps
  assertElimDefs
  dfAnalyzeWidenDefs
  dfgAnalysisProps
  dfgSoundStep
  execEquivParamProps
  finite_map
  list
  passSharedDefs
  passSharedProps
  passSimulationDefs
  passSimulationProps
  rangeAnalysisDefs
  rangeAnalysisProofs
  rangeEvalDefs
  rangeEvalProofs
  stateEquiv
  stateEquivProps
  valueRangeDefs
  variableRangeAnalysisProps
  venomExecProps
  venomExecSemantics
  venomInst
  venomInstProps
  venomState
  venomWf
  worklistDefs

(* Bridge: run_block → exec_block when vs_inst_idx = 0 *)
Triviality run_block_is_exec_block[local]:
  s.vs_inst_idx = 0 ==> run_block f c bb s = exec_block f c bb s
Proof
  strip_tac >> simp[run_block_def] >>
  Cases_on `s` >> gvs[venom_state_fn_updates]
QED

(* ===== Helper: range_excludes_zero + in_range ==> w <> 0w ===== *)

Theorem in_range_excludes_zero_nonzero[local]:
  !r w. in_range r w /\ range_excludes_zero r ==> w <> 0w
Proof
  Cases_on `r` >> simp[in_range_def, range_excludes_zero_def] >>
  rpt strip_tac >> gvs[] >>
  CCONTR_TAC >> gvs[integer_wordTheory.word_0_w2i] >>
  intLib.ARITH_TAC
QED

(* ASSERT semantics: avoids unfolding 92-opcode step_inst_base_def *)
Theorem step_inst_assert_1:
  !fuel ctx inst s op.
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [op] ==>
    step_inst fuel ctx inst s =
      case eval_operand op s of
        NONE => Error "undefined operand"
      | SOME cond =>
          if cond = 0w
          then Abort Revert_abort (revert_state (set_returndata [] s))
          else OK s
Proof
  rpt strip_tac >> simp[step_inst_def, step_inst_base_def]
QED

Theorem step_inst_assert_bad_arity[local]:
  !fuel ctx inst s.
    inst.inst_opcode = ASSERT ==>
    (inst.inst_operands = [] ==>
       step_inst fuel ctx inst s = Error "assert requires 1 operand") /\
    (!a b rest. inst.inst_operands = a::b::rest ==>
       step_inst fuel ctx inst s = Error "assert requires 1 operand")
Proof
  rpt strip_tac >> simp[step_inst_def, step_inst_base_def]
QED

(* in_range_state implies in_range for any looked-up variable *)
Theorem in_range_state_lookup[local]:
  !rs env v w.
    in_range_state rs env /\ FLOOKUP env v = SOME w ==>
    in_range (rs_lookup rs v) w
Proof
  rpt strip_tac >>
  simp[rs_lookup_def] >>
  Cases_on `FLOOKUP rs v` >> simp[in_range_def] >>
  fs[in_range_state_def] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

(* ===== Per-instruction simulation ===== *)

(* Core: assert_elim_inst satisfies analysis_inst_simulates_1 *)
(* Simulation conjunct: ASSERT transform preserves behavior *)
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
      imp_res_tac in_range_state_lookup >>
      imp_res_tac in_range_excludes_zero_nonzero >>
      gvs[lift_result_def, state_equiv_refl])
  (* Label case: identity *)
  >> metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl]
QED

Theorem assert_elim_inst_simulates_1[local]:
  analysis_inst_simulates_1
    (state_equiv {}) (execution_equiv {})
    range_sound assert_elim_inst
Proof
  simp[analysis_inst_simulates_1_def] >> rpt conj_tac
  >- ACCEPT_TAC assert_elim_sim
  (* 2. Terminators preserved *)
  >- (rpt strip_tac >> simp[assert_elim_inst_def] >>
      Cases_on `inst.inst_opcode` >> fs[is_terminator_def])
  (* 3. INVOKE preserved *)
  >- (rpt strip_tac >> simp[assert_elim_inst_def])
  (* 4. Non-term non-INVOKE preserved *)
  >- (rpt strip_tac >> gvs[assert_elim_inst_def] >>
      BasicProvers.every_case_tac >>
      gvs[mk_nop_inst_def, is_terminator_def])
QED

Theorem assert_elim_inst_simulates_proof:
  analysis_inst_simulates
    (state_equiv {}) (execution_equiv {})
    range_sound
    (\v inst. [assert_elim_inst v inst])
Proof
  irule analysis_inst_simulates_from_1 >>
  ACCEPT_TAC assert_elim_inst_simulates_1
QED

(* ===== Function-level correctness ===== *)

(* transfer_sound for range analysis — shared by all range-based passes *)
Theorem range_transfer_sound:
  !fn. transfer_sound range_sound range_transfer_opt
         (dfg_build_function fn, fn.fn_blocks)
Proof
  simp[transfer_sound_def] >> rpt strip_tac >>
  Cases_on `v` >> fs[range_sound_def, range_transfer_opt_def, LET_THM] >>
  irule per_inst_range_sound
  >- (qexistsl_tac [`run_ctx`, `fuel`, `s`] >>
      simp[in_range_state_def, FLOOKUP_DEF])
  >- (qexistsl_tac [`run_ctx`, `fuel`, `s`] >> simp[])
QED

(* range_sound stable under state_equiv {} *)
Theorem range_sound_state_equiv:
  !v s1 s2. state_equiv {} s1 s2 /\ range_sound v s1 ==>
             range_sound v s2
Proof
  rpt strip_tac >> Cases_on `v` >> fs[range_sound_def] >>
  fs[in_range_state_def] >> rpt strip_tac >>
  `FLOOKUP s1.vs_vars v = SOME w` by
    (qpat_x_assum `state_equiv _ _ _` mp_tac >>
     simp[state_equiv_def, execution_equiv_def, lookup_var_def] >>
     metis_tac[]) >>
  res_tac
QED

(* ===== Pre-instantiated framework lemma for range analysis ===== *)

(* Specializes df_analysis_pass_correct_widen_sound_inv to range analysis
   parameters. Eliminates ISPECL + standard obligations. Reusable across
   all range-based passes. *)
Theorem range_analysis_pass_correct:
  !fn sound state_inv f.
    let ra = range_analyze fn in
      transfer_sound sound range_transfer_opt
        (dfg_build_function fn, fn.fn_blocks) /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at NONE ra bb.bb_label 0) s /\
         state_inv s /\ exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
         sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
         state_inv v) /\
      analysis_inst_simulates (state_equiv {}) (execution_equiv {}) sound f /\
      wf_function fn /\ fn_inst_wf fn /\
      (!v s1 s2. state_equiv {} s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. state_equiv {} s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. state_equiv {} s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\ sound (df_widen_at NONE ra s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
          (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
            (analysis_function_transform_widen NONE ra f fn) s)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Instantiate framework with range analysis params, folded to range_analyze *)
  mp_tac (
    REWRITE_RULE [SIMP_RULE std_ss [LET_THM] (GSYM range_analyze_def)]
    (BETA_RULE (PURE_REWRITE_RULE [LET_DEF]
    (ISPECL [
      ``state_equiv {} : venom_state -> venom_state -> bool``,
      ``execution_equiv {} : venom_state -> venom_state -> bool``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``sound : (string |-> value_range) option
          -> venom_state -> bool``,
      ``state_inv : venom_state -> bool``,
      ``f : (string |-> value_range) option
          -> instruction -> instruction list``]
    analysisSimPropsTheory.df_analysis_pass_correct_widen_sound_inv)))) >>
  impl_tac >- (
    rpt conj_tac
    >- simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel]
    >- metis_tac[state_equiv_trans]
    >- metis_tac[execution_equiv_trans]
    >- (mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[])
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC (* wf_function *)
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

(* Specializes df_analysis_pass_correct_widen_sound_inv2 to range analysis.
   Unlike range_analysis_pass_correct, the per-inst sim gets state_inv and
   inst_wf, and there is an obligation to prove state_inv preserved through
   step_inst (with MEM context). Used by overflow_elim, algebraic_opt. *)
Theorem range_analysis_pass_correct_inv2:
  !fn state_inv f.
    let ra = range_analyze fn in
      (* Successor soundness with state_inv *)
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
         state_inv s /\ exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
         range_sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
         state_inv v) /\
      (* Per-inst sim: gets range_sound + state_inv + inst_wf *)
      (!fuel ctx v inst s.
         range_sound v s /\ state_inv (s with vs_inst_idx := 0) /\
         inst_wf inst ==>
         (?e. step_inst fuel ctx inst s = Error e) \/
         lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
           (step_inst fuel ctx inst s)
           (run_insts fuel ctx (f v inst) s)) /\
      inst_transform_structural f /\
      wf_function fn /\ fn_inst_wf fn /\
      (* state_inv stable under state_equiv {} *)
      (!s1 s2. state_equiv {} s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (* state_inv preserved through step_inst from fn blocks *)
      (!fuel ctx bb inst s s'.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         inst_wf inst /\
         state_inv (s with vs_inst_idx := 0) /\
         step_inst fuel ctx inst s = OK s' ==>
         state_inv (s' with vs_inst_idx := 0))
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        range_sound (df_widen_at NONE ra s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
          (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
            (analysis_function_transform_widen NONE ra f fn) s)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  mp_tac (
    REWRITE_RULE [SIMP_RULE std_ss [LET_THM] (GSYM range_analyze_def)]
    (BETA_RULE (PURE_REWRITE_RULE [LET_DEF]
    (ISPECL [
      ``state_equiv {} : venom_state -> venom_state -> bool``,
      ``execution_equiv {} : venom_state -> venom_state -> bool``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``range_sound``,
      ``state_inv : venom_state -> bool``,
      ``f : (string |-> value_range) option
          -> instruction -> instruction list``]
    analysisSimPropsTheory.df_analysis_pass_correct_widen_sound_inv2)))) >>
  impl_tac >- (
    rpt conj_tac
    (* valid_state_rel *)
    >- simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel]
    (* R_ok trans *)
    >- metis_tac[state_equiv_trans]
    (* R_term trans *)
    >- metis_tac[execution_equiv_trans]
    (* is_fixpoint *)
    >- (mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[])
    (* transfer_sound_wf: from range_transfer_sound (transfer_sound => _wf) *)
    >- (simp[analysisSimDefsTheory.transfer_sound_wf_def] >>
        mp_tac (SPEC_ALL range_transfer_sound) >>
        simp[analysisSimDefsTheory.transfer_sound_def] >>
        metis_tac[])
    (* successor *)
    >- first_assum ACCEPT_TAC
    (* per-inst sim *)
    >- first_assum ACCEPT_TAC
    (* inst_transform_structural *)
    >- first_assum ACCEPT_TAC
    (* wf_function *)
    >- first_assum ACCEPT_TAC
    (* fn_inst_wf *)
    >- first_assum ACCEPT_TAC
    (* range_sound stable under state_equiv {} *)
    >- metis_tac[range_sound_state_equiv]
    (* state_inv stable *)
    >- first_assum ACCEPT_TAC
    (* per-step state_inv *)
    >- first_assum ACCEPT_TAC
    (* lookup_var stable under state_equiv {} *)
    >> (rpt strip_tac >>
        fs[state_equiv_def, execution_equiv_def, lookup_var_def])) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

(* Generalizes range_analysis_pass_correct_inv2 to arbitrary exclusion sets.
   Passes with non-empty R_ok/R_term (e.g. algebraic_opt with ao_fresh_set)
   must additionally discharge: range_sound stability under R_ok,
   lookup_var stability for fn operands under R_ok. *)
Theorem range_analysis_pass_correct_excl:
  !fn excl state_inv f.
    let ra = range_analyze fn in
      (* Successor soundness with state_inv *)
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
         state_inv s /\ exec_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
         range_sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
         state_inv v) /\
      (* Per-inst sim: gets range_sound + state_inv + inst_wf *)
      (!fuel ctx v inst s.
         range_sound v s /\ state_inv (s with vs_inst_idx := 0) /\
         inst_wf inst ==>
         (?e. step_inst fuel ctx inst s = Error e) \/
         lift_result (state_equiv excl) (execution_equiv excl) (execution_equiv excl)
           (step_inst fuel ctx inst s)
           (run_insts fuel ctx (f v inst) s)) /\
      inst_transform_structural f /\
      wf_function fn /\ fn_inst_wf fn /\
      (* range_sound stable under state_equiv excl *)
      (!v s1 s2. state_equiv excl s1 s2 /\ range_sound v s1 ==>
         range_sound v s2) /\
      (* state_inv stable under state_equiv excl *)
      (!s1 s2. state_equiv excl s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (* state_inv preserved through step_inst from fn blocks *)
      (!fuel ctx bb inst s s'.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         inst_wf inst /\
         state_inv (s with vs_inst_idx := 0) /\
         step_inst fuel ctx inst s = OK s' ==>
         state_inv (s' with vs_inst_idx := 0)) /\
      (* lookup_var stable under state_equiv excl for fn operands *)
      (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. state_equiv excl s1 s2 ==>
           lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        range_sound (df_widen_at NONE ra s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result (state_equiv excl) (execution_equiv excl) (execution_equiv excl)
          (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
            (analysis_function_transform_widen NONE ra f fn) s)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  mp_tac (
    REWRITE_RULE [SIMP_RULE std_ss [LET_THM] (GSYM range_analyze_def)]
    (BETA_RULE (PURE_REWRITE_RULE [LET_DEF]
    (ISPECL [
      ``state_equiv excl : venom_state -> venom_state -> bool``,
      ``execution_equiv excl : venom_state -> venom_state -> bool``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``range_sound``,
      ``state_inv : venom_state -> bool``,
      ``f : (string |-> value_range) option
          -> instruction -> instruction list``]
    analysisSimPropsTheory.df_analysis_pass_correct_widen_sound_inv2)))) >>
  impl_tac >- (
    rpt conj_tac
    (* valid_state_rel *)
    >- simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel]
    (* R_ok trans *)
    >- metis_tac[state_equiv_trans]
    (* R_term trans *)
    >- metis_tac[execution_equiv_trans]
    (* is_fixpoint *)
    >- (mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[])
    (* transfer_sound_wf *)
    >- (simp[analysisSimDefsTheory.transfer_sound_wf_def] >>
        mp_tac (SPEC_ALL range_transfer_sound) >>
        simp[analysisSimDefsTheory.transfer_sound_def] >>
        metis_tac[])
    (* successor *)
    >- first_assum ACCEPT_TAC
    (* per-inst sim *)
    >- first_assum ACCEPT_TAC
    (* inst_transform_structural *)
    >- first_assum ACCEPT_TAC
    (* wf_function *)
    >- first_assum ACCEPT_TAC
    (* fn_inst_wf *)
    >- first_assum ACCEPT_TAC
    (* range_sound stable *)
    >- first_assum ACCEPT_TAC
    (* state_inv stable *)
    >- first_assum ACCEPT_TAC
    (* per-step state_inv *)
    >- first_assum ACCEPT_TAC
    (* lookup_var stable *)
    >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED

(* NOTE: range_analysis_pass_correct_excl_idx was planned here but moved to
   algebraicOptProofs where range_transfer_opt_disjoint_restricted is available.
   The universal range_sound stability in range_analysis_pass_correct_excl is
   unprovable for non-empty excl sets — need the disjoint restriction. *)

(* ===== Range analysis fixpoint wrappers ===== *)
(* These eliminate the 15-line ISPECL boilerplate for dfAnalyzeWiden theorems
   specialized to range analysis. Used by range_exit_sound, range_widen_at_some,
   range_successor_sound, and future range-based passes. *)


(* Intra-block transfer: df_widen_at at SUC idx = transfer applied to idx *)
Theorem range_intra_transfer:
  !fn lbl bb idx.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions ==>
    df_widen_at NONE (range_analyze fn) lbl (SUC idx) =
    range_transfer_opt (dfg_build_function fn, fn.fn_blocks)
      (EL idx bb.bb_instructions)
      (df_widen_at NONE (range_analyze fn) lbl idx)
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
    (ISPECL [
      ``Forward``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``lbl : string``,
      ``bb : basic_block``,
      ``idx : num``]
    dfAnalyzeWidenPropsTheory.df_widen_at_intra_transfer))) >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
  simp[]
QED

(* Inter-block transfer: df_widen_at at position 0 = df_widen_entry *)
Theorem range_entry_eq:
  !fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    df_widen_at NONE (range_analyze fn) lbl 0 =
    df_widen_entry NONE (range_analyze fn) lbl
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
    (ISPECL [
      ``Forward``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``lbl : string``,
      ``bb : basic_block``]
    dfAnalyzeWidenPropsTheory.df_widen_at_inter_transfer))) >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
  simp[]
QED

(* Helper: connect df_fold_block fst output to df_widen_at *)
(* Bridge: fold result fv = df_widen_at at exit position.
   Uses df_fold_forward_midpoint + intra_transfer. *)
(* Helper: fold result agrees with df_widen_at at every position *)
Triviality df_fold_widen_at_agree:
  !n transfer lbl instrs entry fv im fn bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    transfer = range_transfer_opt (dfg_build_function fn, fn.fn_blocks) /\
    instrs = bb.bb_instructions /\
    entry = df_widen_entry NONE (range_analyze fn) lbl /\
    df_fold_forward transfer lbl instrs 0 entry FEMPTY = (fv, im) /\
    n <= LENGTH instrs ==>
    FLOOKUP im (lbl, n) = SOME (df_widen_at NONE (range_analyze fn) lbl n)
Proof
  Induct >> rpt strip_tac
  >- ((* base: n=0, entry *)
    imp_res_tac dfAnalyzeProofsTheory.df_fold_forward_at >>
    `df_widen_at NONE (range_analyze fn) lbl 0 =
     df_widen_entry NONE (range_analyze fn) lbl` by (
      irule (SIMP_RULE std_ss [LET_THM] range_entry_eq) >> simp[]) >>
    gvs[])
  >> (* inductive: n = SUC n' *)
  gvs[] >>
  `n < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  `FLOOKUP im (lbl, n) =
   SOME (df_widen_at NONE (range_analyze fn) lbl n)` by (
    first_x_assum match_mp_tac >> simp[]) >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_forward_at >>
  `df_widen_at NONE (range_analyze fn) lbl (SUC n) =
   range_transfer_opt (dfg_build_function fn, fn.fn_blocks)
     (EL n bb.bb_instructions)
     (df_widen_at NONE (range_analyze fn) lbl n)` by (
    irule (SIMP_RULE std_ss [LET_THM] range_intra_transfer) >> simp[]) >>
  fs[]
QED

Theorem df_fold_fv_eq_widen_at:
  !fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    let ra = range_analyze fn in
    let entry = df_widen_entry NONE ra lbl in
    let (fv, im) = df_fold_block Forward
      (range_transfer_opt (dfg_build_function fn, fn.fn_blocks))
      lbl bb.bb_instructions entry in
    fv = df_widen_at NONE ra lbl (LENGTH bb.bb_instructions)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  pairarg_tac >> simp[] >>
  fs[dfAnalyzeDefsTheory.df_fold_block_def] >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_forward_at >>
  (* fv = THE (FLOOKUP im (lbl, LENGTH instrs)) *)
  (* Show FLOOKUP im (lbl, LENGTH instrs) = SOME (df_widen_at ...) *)
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
    `range_transfer_opt (dfg_build_function fn, fn.fn_blocks)`,
    `lbl`, `bb.bb_instructions`,
    `df_widen_entry NONE (range_analyze fn) lbl`,
    `fv`, `im`, `fn`, `bb`] df_fold_widen_at_agree) >>
  simp[]
QED

(* Precompute the ISPECL of process_fixpoint_absorbs for range analysis *)
fun mk_range_pfa () =
  CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
  (SIMP_RULE std_ss [LET_THM, dfAnalyzeDefsTheory.direction_case_def]
  (SIMP_RULE std_ss [LET_THM]
  (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
  (ISPECL [
    ``Forward``,
    ``NONE : (string |-> value_range) option``,
    ``range_join_opt``,
    ``range_widen_opt : (string |-> value_range) option
        -> (string |-> value_range) option
        -> (string |-> value_range) option``,
    ``WIDEN_THRESHOLD``,
    ``range_transfer_opt``,
    ``range_edge_transfer_opt``,
    ``(dfg_build_function fn, fn.fn_blocks)``,
    ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
        (fn_entry_label fn)``,
    ``cfg_analyze fn``,
    ``fn.fn_blocks``,
    ``lbl : string``,
    ``range_analyze fn``]
  dfAnalyzeWidenProofsTheory.process_fixpoint_absorbs))));

(* Boundary absorption at fixpoint: boundary = join(boundary, exit_val) *)
Theorem range_fixpoint_absorbs:
  !fn lbl.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    let ra = range_analyze fn in
    let cfg = cfg_analyze fn in
    let neighbors = cfg_preds_of cfg lbl in
    let edge_vals = MAP (\nbr. range_edge_transfer_opt
          (dfg_build_function fn, fn.fn_blocks) nbr lbl
          (df_widen_boundary NONE ra nbr)) neighbors in
    let joined = (case edge_vals of
        [] => (case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
                 NONE => NONE
               | SOME (ev_lbl, v) => if lbl = ev_lbl then v else NONE)
      | v4::v5 => FOLDL range_join_opt NONE edge_vals) in
    let entry = (if df_widen_visits ra lbl >= WIDEN_THRESHOLD
                 then range_widen_opt (df_widen_entry NONE ra lbl) joined
                 else joined) in
      entry = df_widen_entry NONE ra lbl /\
      range_join_opt (df_widen_boundary NONE ra lbl)
        (df_widen_at NONE ra lbl
          (case lookup_block lbl fn.fn_blocks of
             NONE => 0
           | SOME bb => LENGTH bb.bb_instructions)) =
      df_widen_boundary NONE ra lbl
Proof
  rpt strip_tac
  \\ simp_tac std_ss [LET_THM]
  \\ mp_tac (mk_range_pfa ())
  \\ impl_tac
  >- (mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >>
      simp[is_fixpoint_def, EVERY_MEM])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ strip_tac
  \\ conj_tac
  >- first_assum ACCEPT_TAC
  \\ Cases_on `lookup_block lbl fn.fn_blocks`
  >- ((* NONE case: impossible - reachable labels have blocks *)
      imp_res_tac dfAnalyzeProofsTheory.cfg_dfs_pre_subset_fn_labels >>
      gvs[fn_labels_def, MEM_MAP, wf_function_def] >>
      imp_res_tac venomExecPropsTheory.MEM_lookup_block >> gvs[])
  \\ rename1 `SOME bb`
  \\ mp_tac (SIMP_RULE std_ss [LET_THM] df_fold_fv_eq_widen_at)
  \\ disch_then (qspecl_then [`fn`, `lbl`, `bb`] mp_tac)
  \\ simp[] >> strip_tac
  \\ Cases_on `df_fold_block Forward
        (range_transfer_opt (dfg_build_function fn,fn.fn_blocks)) lbl
        bb.bb_instructions
        (df_widen_entry NONE (range_analyze fn) lbl)`
  \\ gvs[]
QED

(* ===== Range soundness at successor entry ===== *)

(* Exit soundness: range_sound at block entry ==> range_sound at block exit.
   Uses transfer_sound_exit via widen_to_df bridge. *)
Theorem range_exit_sound:
  !fn bb fuel run_ctx s v.
    let ra = range_analyze fn in
      wf_function fn /\
      fn_inst_wf fn /\
      ALL_DISTINCT (fn_labels fn) /\
      (!bb. MEM bb fn.fn_blocks ==>
        !i. i < LENGTH bb.bb_instructions - 1 ==>
          ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      s.vs_inst_idx = 0 /\
      range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
      run_block fuel run_ctx bb s = OK v ==>
      range_sound (df_widen_at NONE ra bb.bb_label
        (LENGTH bb.bb_instructions)) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  (* Bridge: run_block → exec_block *)
  `exec_block fuel run_ctx bb s = OK v` by
    metis_tac[run_block_is_exec_block] >>
  (* Block setup boilerplate *)
  `bb.bb_instructions <> []` by
    (imp_res_tac venomExecProofsTheory.exec_block_ok_nonempty) >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  qabbrev_tac `ti = PRE (LENGTH bb.bb_instructions)` >>
  `ti < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`]) >>
  `is_terminator (EL ti bb.bb_instructions).inst_opcode` by (
    `bb_well_formed bb` by (fs[wf_function_def] >> metis_tac[]) >>
    fs[bb_well_formed_def, Abbr `ti`] >>
    Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
  `!j. j < ti ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> first_x_assum (qspec_then `bb` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspec_then `j` mp_tac) >>
    impl_tac >- fs[Abbr `ti`] >> simp[]) >>
  `SUC ti = LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by (
    qpat_assum `ALL_DISTINCT _` mp_tac >>
    simp_tac std_ss [fn_labels_def] >> strip_tac >>
    metis_tac[venomExecPropsTheory.MEM_lookup_block]) >>
  (* Widen-to-df bridge *)
  qabbrev_tac `result = widen_to_df (range_analyze fn)` >>
  `!idx. df_widen_at NONE (range_analyze fn) bb.bb_label idx =
         df_at NONE result bb.bb_label idx` by
    simp[Abbr `result`, analysisSimProofsTheory.widen_to_df_def,
         dfAnalyzeWidenDefsTheory.df_widen_at_def,
         dfAnalyzeDefsTheory.df_at_def] >>
  (* Establish intra-transfer equations in df_widen_at terms first *)
  `!idx. SUC idx <= LENGTH bb.bb_instructions ==>
     df_widen_at NONE (range_analyze fn) bb.bb_label (SUC idx) =
     range_transfer_opt (dfg_build_function fn, fn.fn_blocks)
       (EL idx bb.bb_instructions)
       (df_widen_at NONE (range_analyze fn) bb.bb_label idx)` by (
    rpt strip_tac >>
    mp_tac (SIMP_RULE std_ss [LET_THM]
      (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
      (ISPECL [
        ``Forward``,
        ``NONE : (string |-> value_range) option``,
        ``range_join_opt``,
        ``range_widen_opt : (string |-> value_range) option
            -> (string |-> value_range) option
            -> (string |-> value_range) option``,
        ``WIDEN_THRESHOLD``,
        ``range_transfer_opt``,
        ``range_edge_transfer_opt``,
        ``(dfg_build_function fn, fn.fn_blocks)``,
        ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
            (fn_entry_label fn)``,
        ``fn : ir_function``,
        ``bb.bb_label``,
        ``bb : basic_block``,
        ``idx : num``]
      dfAnalyzeWidenPropsTheory.df_widen_at_intra_transfer))) >>
    impl_tac >- (
      conj_tac >- first_assum ACCEPT_TAC >>
      mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
    simp[]) >>
  (* Convert to df_at terms using bridge *)
  `!idx. SUC idx <= LENGTH bb.bb_instructions ==>
     df_at NONE result bb.bb_label (SUC idx) =
     range_transfer_opt (dfg_build_function fn, fn.fn_blocks)
       (EL idx bb.bb_instructions)
       (df_at NONE result bb.bb_label idx)` by metis_tac[] >>
  (* Apply transfer_sound_exit *)
  mp_tac (ISPECL [
    ``state_equiv {} : venom_state -> venom_state -> bool``,
    ``execution_equiv {} : venom_state -> venom_state -> bool``,
    ``range_sound``,
    ``range_transfer_opt``,
    ``(dfg_build_function fn, fn.fn_blocks)``,
    ``bb : basic_block``,
    ``NONE : (string |-> value_range) option``,
    ``result : (string |-> value_range) option df_state``]
    analysisSimPropsTheory.transfer_sound_exit) >>
  impl_tac >- (
    rpt conj_tac
    >- simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel]
    >- metis_tac[range_transfer_sound]
    >- metis_tac[range_sound_state_equiv]
    >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`fuel`, `run_ctx`, `s`, `v`, `ti`] mp_tac) >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  `df_at NONE result bb.bb_label (LENGTH bb.bb_instructions) =
   range_transfer_opt (dfg_build_function fn, fn.fn_blocks)
     (EL ti bb.bb_instructions) (df_at NONE result bb.bb_label ti)` by
    (first_x_assum (qspec_then `ti` mp_tac) >> simp[]) >>
  simp[]
QED

(* ===== Successor soundness (main) ===== *)

(* range_transfer_opt always returns SOME *)
Theorem range_transfer_opt_is_some:
  !ctx inst v. ?rs. range_transfer_opt ctx inst v = SOME rs
Proof
  rpt gen_tac >> Cases_on `v` >>
  simp[range_transfer_opt_def, LET_THM]
QED

(* df_widen_at is SOME at any position >= 1 in a non-empty block,
   since range_transfer_opt always produces SOME. *)
Theorem range_widen_at_some:
  !fn bb n.
    let ra = range_analyze fn in
      wf_function fn /\
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      ALL_DISTINCT (fn_labels fn) /\
      0 < n /\ n <= LENGTH bb.bb_instructions ==>
      ?rs. df_widen_at NONE ra bb.bb_label n = SOME rs
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by (
    irule venomExecPropsTheory.MEM_lookup_block >>
    qpat_assum `ALL_DISTINCT _` mp_tac >>
    simp_tac std_ss [fn_labels_def] >> metis_tac[]) >>
  Induct_on `n` >> simp[] >> rpt strip_tac >>
  (* Get the intra-transfer equation at position n *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
    (ISPECL [
      ``Forward``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``bb.bb_label``,
      ``bb : basic_block``,
      ``n : num``]
    dfAnalyzeWidenPropsTheory.df_widen_at_intra_transfer))) >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
  simp[] >> strip_tac >>
  metis_tac[range_transfer_opt_is_some]
QED

(* Helper: range_widen_opt at fixpoint produces NONE, SOME FEMPTY, or the joined value.
   In all cases either trivially sound or reduces to showing joined is sound. *)
Theorem range_widen_opt_fixpoint_cases:
  !old joined.
    range_widen_opt old joined = old ==>
    old = NONE \/ old = SOME FEMPTY \/ old = joined
Proof
  Cases_on `old` >> Cases_on `joined` >>
  simp[range_widen_opt_def] >>
  rpt strip_tac >> BasicProvers.every_case_tac >> fs[]
QED

(* Helper: JNZ branch condition for range_branch_refine_sound.
   When JNZ always has distinct labels, we can derive the branch condition
   from run_block_jnz_condition. *)
Theorem jnz_branch_condition_from_run_block:
  !fn bb fuel run_ctx s v succ.
    run_block fuel run_ctx bb s = OK v /\
    succ = v.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) ==>
    !bb' cond_op true_lbl false_lbl.
      lookup_block bb.bb_label fn.fn_blocks = SOME bb' /\
      bb'.bb_instructions <> [] /\
      (LAST bb'.bb_instructions).inst_opcode = JNZ /\
      (LAST bb'.bb_instructions).inst_operands =
        [cond_op; Label true_lbl; Label false_lbl] ==>
      !var. cond_op = Var var ==>
        ?w. FLOOKUP v.vs_vars var = SOME w /\
            (succ = true_lbl ==> w <> 0w) /\
            (succ = false_lbl ==> w = 0w)
Proof
  rpt strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `bb' = bb` by fs[] >> BasicProvers.VAR_EQ_TAC >>
  `true_lbl <> false_lbl` by (
    CCONTR_TAC >> fs[] >> res_tac) >>
  mp_tac run_block_jnz_condition >>
  disch_then (qspecl_then [`fuel`, `run_ctx`, `bb`, `s`, `v`,
    `var`, `true_lbl`, `false_lbl`] mp_tac) >>
  simp[]
QED

(* Helper: combines jnz_branch_condition_from_run_block with
   range_branch_refine_sound to get in_range_state of the refined range
   at a successor, given run_block + boundary soundness. *)
Theorem range_branch_refine_after_run_block:
  !fn bb fuel run_ctx s v succ boundary_rs.
    run_block fuel run_ctx bb s = OK v /\
    succ = v.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    in_range_state boundary_rs v.vs_vars /\
    dfg_sound (dfg_build_function fn) v.vs_vars ==>
    in_range_state (range_branch_refine (dfg_build_function fn)
      fn.fn_blocks bb.bb_label succ boundary_rs) v.vs_vars
Proof
  rpt strip_tac >>
  mp_tac range_branch_refine_sound >>
  disch_then (qspecl_then [`dfg_build_function fn`, `fn.fn_blocks`,
    `bb.bb_label`, `succ`, `boundary_rs`, `v.vs_vars`] mp_tac) >>
  `!bb' cond_op true_lbl false_lbl.
      lookup_block bb.bb_label fn.fn_blocks = SOME bb' /\
      bb'.bb_instructions <> [] /\
      (LAST bb'.bb_instructions).inst_opcode = JNZ /\
      (LAST bb'.bb_instructions).inst_operands =
        [cond_op; Label true_lbl; Label false_lbl] ==>
      !var. cond_op = Var var ==>
        ?w. FLOOKUP v.vs_vars var = SOME w /\
            (succ = true_lbl ==> w <> 0w) /\
            (succ = false_lbl ==> w = 0w)` by (
    mp_tac jnz_branch_condition_from_run_block >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`,
      `succ`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >> first_assum ACCEPT_TAC)
  \\ impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
  \\ strip_tac
QED

Theorem range_edge_transfer_opt_some:
  !dfg bbs pred succ rs.
    range_edge_transfer_opt (dfg, bbs) pred succ (SOME rs) =
    SOME (range_branch_refine dfg bbs pred succ rs)
Proof
  simp[range_edge_transfer_opt_def]
QED

(* Successor soundness: after running a block at a fixpoint,
   the successor has range_sound, dfg_sound+ops_defined, and is in cfg_dfs_pre.
   Requires ssa_form + dfg_sound for edge_transfer soundness. *)
(* range_sound at successor entry point *)
Theorem range_sound_at_successor:
  !fn bb fuel run_ctx s v.
    let ra = range_analyze fn in
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
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
      range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
      dfg_sound (dfg_build_function fn) s.vs_vars /\
      (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
         vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
         u IN FDOM s.vs_vars) /\
      run_block fuel run_ctx bb s = OK v /\
      dfg_sound (dfg_build_function fn) v.vs_vars /\
      MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label) ==>
      range_sound (df_widen_at NONE ra v.vs_current_bb 0) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by (
    irule venomExecPropsTheory.MEM_lookup_block >>
    fs[fn_labels_def]) >>
  (* Exit soundness *)
  `range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label
     (LENGTH bb.bb_instructions)) v` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_exit_sound) >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac) >>
    simp[]) >>
  (* Exit value is SOME *)
  `?exit_rs. df_widen_at NONE (range_analyze fn) bb.bb_label
     (LENGTH bb.bb_instructions) = SOME exit_rs` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_widen_at_some) >>
    disch_then (qspecl_then [`fn`, `bb`, `LENGTH bb.bb_instructions`] mp_tac) >>
    simp[] >> impl_tac >- (Cases_on `bb.bb_instructions` >> fs[]) >>
    simp[]) >>
  qabbrev_tac `ra = range_analyze fn` >>
  qabbrev_tac `succ = v.vs_current_bb` >>
  `MEM succ (cfg_analyze fn).cfg_dfs_pre` by (
    imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
    gvs[EVERY_MEM]) >>
  (* Fixpoint absorption at bb.bb_label *)
  `range_join_opt (df_widen_boundary NONE ra bb.bb_label)
     (df_widen_at NONE ra bb.bb_label (LENGTH bb.bb_instructions)) =
   df_widen_boundary NONE ra bb.bb_label` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint_absorbs) >>
    disch_then (qspecl_then [`fn`, `bb.bb_label`] mp_tac) >>
    simp[Abbr `ra`]) >>
  (* Boundary is SOME *)
  `?boundary_rs. df_widen_boundary NONE ra bb.bb_label = SOME boundary_rs` by (
    CCONTR_TAC >> gvs[] >>
    Cases_on `df_widen_boundary NONE ra bb.bb_label` >> gvs[] >>
    fs[range_join_opt_def]) >>
  `range_join_opt (SOME boundary_rs) (SOME exit_rs) = SOME boundary_rs` by
    gvs[] >>
  `in_range_state boundary_rs v.vs_vars` by (
    mp_tac (Q.SPECL [`SOME boundary_rs`, `exit_rs`, `v`]
      range_join_opt_some_sound_right) >>
    simp[range_sound_def] >> gvs[range_sound_def]) >>
  (* Successor lookup + pred *)
  `?succ_bb. lookup_block succ fn.fn_blocks = SOME succ_bb` by (
    `MEM succ (fn_labels fn)` by (
      `cfg_reachable_of (cfg_analyze fn) succ` by (
        imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
        fs[pred_setTheory.EXTENSION, Abbr `succ`]) >>
      metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels]) >>
    fs[fn_labels_def, MEM_MAP] >>
    metis_tac[venomExecPropsTheory.MEM_lookup_block, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) succ)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond, Abbr `succ`] >>
  (* Entry = df_widen_entry *)
  `df_widen_at NONE ra succ 0 = df_widen_entry NONE ra succ` by (
    mp_tac range_entry_eq >>
    disch_then (qspecl_then [`fn`, `succ`, `succ_bb`] mp_tac) >>
    simp[Abbr `ra`, Abbr `succ`]) >>
  simp[] >>
  (* Fixpoint at succ *)
  qabbrev_tac `neighbors = cfg_preds_of (cfg_analyze fn) succ` >>
  qabbrev_tac `edge_vals = MAP (\nbr. range_edge_transfer_opt
        (dfg_build_function fn, fn.fn_blocks) nbr succ
        (df_widen_boundary NONE ra nbr)) neighbors` >>
  qabbrev_tac `joined = (case edge_vals of
      [] => (case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
               NONE => NONE
             | SOME (ev_lbl, v') => if succ = ev_lbl then v' else NONE)
    | v4::v5 => FOLDL range_join_opt NONE edge_vals)` >>
  qabbrev_tac `entry = (if df_widen_visits ra succ >= WIDEN_THRESHOLD
               then range_widen_opt (df_widen_entry NONE ra succ) joined
               else joined)` >>
  `entry = df_widen_entry NONE ra succ` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint_absorbs) >>
    disch_then (qspecl_then [`fn`, `succ`] mp_tac) >>
    simp[Abbr `ra`, Abbr `succ`] >>
    simp_tac std_ss [LET_THM] >> strip_tac >>
    unabbrev_all_tac >> gvs[]) >>
  Cases_on `entry = NONE` >- gvs[range_sound_def] >>
  Cases_on `entry = SOME FEMPTY` >- gvs[range_sound_def, in_range_state_def] >>
  `entry = joined` by (
    Cases_on `df_widen_visits ra succ >= WIDEN_THRESHOLD` >> gvs[Abbr `entry`] >>
    metis_tac[range_widen_opt_fixpoint_cases]) >>
  `edge_vals <> []` by (
    CCONTR_TAC >> gvs[Abbr `edge_vals`] >>
    `neighbors = []` by gvs[Abbr `neighbors`] >>
    gvs[Abbr `joined`] >>
    BasicProvers.every_case_tac >> gvs[]) >>
  `?hd tl. edge_vals = hd::tl` by (Cases_on `edge_vals` >> gvs[]) >>
  `joined = FOLDL range_join_opt NONE edge_vals` by
    gvs[Abbr `joined`]
  (* Step 11: MEM *)
  \\ qabbrev_tac `refined_rs = range_branch_refine (dfg_build_function fn)
        fn.fn_blocks bb.bb_label succ boundary_rs`
  \\ `SOME refined_rs = range_edge_transfer_opt (dfg_build_function fn,
       fn.fn_blocks) bb.bb_label succ (df_widen_boundary NONE ra bb.bb_label)`
      by (qunabbrev_tac `refined_rs` >>
          qpat_x_assum `df_widen_boundary NONE ra bb.bb_label = SOME boundary_rs`
            SUBST1_TAC >>
          REWRITE_TAC [GSYM range_edge_transfer_opt_some])
  \\ `MEM (SOME refined_rs) edge_vals` by (
    pop_assum SUBST1_TAC >>
    qunabbrev_tac `edge_vals` >> qunabbrev_tac `neighbors` >>
    REWRITE_TAC [MEM_MAP] >>
    qexists_tac `bb.bb_label` >>
    conj_tac >- (BETA_TAC >> REFL_TAC) >>
    first_assum ACCEPT_TAC)
  (* Step 12: Re-derive JNZ distinct-labels in original form *)
  \\ `!bb' cond true_lbl false_lbl. MEM bb' fn.fn_blocks /\
        (LAST bb'.bb_instructions).inst_opcode = JNZ /\
        (LAST bb'.bb_instructions).inst_operands =
          [cond; Label true_lbl; Label false_lbl] ==>
        true_lbl <> false_lbl` by (
    rpt gen_tac >> strip_tac >> CCONTR_TAC >>
    `true_lbl = false_lbl` by (pop_assum mp_tac >> REWRITE_TAC[]) >>
    BasicProvers.VAR_EQ_TAC >> res_tac)
  (* Step 13: specialize non-terminator hypothesis for bb *)
  \\ `!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> _`
      (qspec_then `bb` mp_tac) >>
    impl_tac >- (first_assum ACCEPT_TAC) >>
    strip_tac >> first_assum ACCEPT_TAC)
  (* Step 14: in_range_state of branch_refine *)
  \\ `in_range_state refined_rs v.vs_vars` by (
    qpat_x_assum `Abbrev (refined_rs = _)` (REWRITE_TAC o single o
      REWRITE_RULE [markerTheory.Abbrev_def])
    \\ qpat_x_assum `Abbrev (succ = _)` (REWRITE_TAC o single o
      REWRITE_RULE [markerTheory.Abbrev_def])
    \\ mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`,
      `v.vs_current_bb`, `boundary_rs`] range_branch_refine_after_run_block)
    \\ REWRITE_TAC[]
    \\ impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
    \\ strip_tac \\ first_assum ACCEPT_TAC)
  (* Step 15: range_sound via FOLDL *)
  \\ `range_sound (FOLDL range_join_opt NONE edge_vals) v` by (
    irule foldl_range_join_opt_sound >>
    qexists_tac `refined_rs` >>
    conj_tac >> first_assum ACCEPT_TAC)
  \\ metis_tac[]
QED

Theorem range_successor_sound:
  !fn bb fuel run_ctx s v.
    let ra = range_analyze fn in
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
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
      range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
      dfg_sound (dfg_build_function fn) s.vs_vars /\
      (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
         vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
         u IN FDOM s.vs_vars) /\
      run_block fuel run_ctx bb s = OK v ==>
      MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
      range_sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
      dfg_sound (dfg_build_function fn) v.vs_vars /\
      (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
         vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
         u IN FDOM v.vs_vars)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  (* Bridge: run_block → exec_block *)
  `exec_block fuel run_ctx bb s = OK v` by
    metis_tac[run_block_is_exec_block] >>
  (* Derive block well-formedness *)
  `bb_well_formed bb` by fs[wf_function_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  (* Successor in cfg_dfs_pre *)
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecPropsTheory.exec_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs] >>
  `MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    (imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
     gvs[EVERY_MEM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (* dfg_sound + ops_defined *)
  `dfg_sound (dfg_build_function fn) v.vs_vars /\
   (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
      vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
      u IN FDOM v.vs_vars)` by (
    mp_tac dfg_sound_run_block >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[])
  (* range_sound via extracted helper *)
  \\ conj_tac >- (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_sound_at_successor) >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >> first_assum ACCEPT_TAC)
  >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

(* dfg_sound is preserved by state_equiv {} because state_equiv {} implies
   vs_vars agreement (via lookup_var agreement with empty excluded set). *)
Theorem dfg_sound_state_equiv:
  !dfg s1 s2. state_equiv {} s1 s2 /\ dfg_sound dfg s1.vs_vars ==>
               dfg_sound dfg s2.vs_vars
Proof
  rpt strip_tac >> imp_res_tac state_equiv_empty_vars_eq >> fs[]
QED

(* Re-derive original JNZ distinct-labels from HOL-simplified form.
   HOL simplifies (!bb cond tl fl. ... ==> tl <> fl) to
   (!bb cond fl. JNZ ==> ops=[...fl;fl] ==> ~MEM bb bbs).
   range_successor_sound needs the original form. *)
Theorem jnz_distinct_labels_from_simplified:
  (!bb cond false_lbl.
     (LAST bb.bb_instructions).inst_opcode = JNZ ==>
     (LAST bb.bb_instructions).inst_operands =
       [cond; Label false_lbl; Label false_lbl] ==>
     ~MEM bb bbs) ==>
  (!bb cond true_lbl false_lbl.
     MEM bb bbs /\
     (LAST bb.bb_instructions).inst_opcode = JNZ /\
     (LAST bb.bb_instructions).inst_operands =
       [cond; Label true_lbl; Label false_lbl] ==>
     true_lbl <> false_lbl)
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[]
QED

(* Successor obligation adapted for the framework call context.
   Uses range_successor_sound but handles the JNZ hypothesis form mismatch. *)
Theorem range_successor_obligation:
  wf_function fn /\ fn_inst_wf fn /\
  (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
     MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
  ALL_DISTINCT (fn_labels fn) /\
  dfg_block_local fn /\
  (!bb. MEM bb fn.fn_blocks ==>
    !i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
  (!bb cond false_lbl.
     (LAST bb.bb_instructions).inst_opcode = JNZ ==>
     (LAST bb.bb_instructions).inst_operands =
       [cond; Label false_lbl; Label false_lbl] ==>
     ~MEM bb fn.fn_blocks) ==>
  !bb fuel run_ctx s v.
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
    range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label 0) s /\
    (dfg_sound (dfg_build_function fn) s.vs_vars /\
     !vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
        vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
        MEM (Var u) dinst.inst_operands ==>
        u IN FDOM s.vs_vars) /\
    exec_block fuel run_ctx bb s = OK v ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    range_sound (df_widen_at NONE (range_analyze fn) v.vs_current_bb 0) v /\
    dfg_sound (dfg_build_function fn) v.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM v.vs_vars)
Proof
  strip_tac
  >> imp_res_tac jnz_distinct_labels_from_simplified
  >> rpt gen_tac >> strip_tac
  >> `run_block fuel run_ctx bb s = OK v` by
       metis_tac[run_block_is_exec_block]
  >> mp_tac (SIMP_RULE std_ss [LET_THM] range_successor_sound)
  >> disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac)
  >> (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC))
  >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

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
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> strip_tac
  \\ simp[assert_elim_function_def, LET_THM]
  \\ mp_tac (SIMP_RULE std_ss [LET_THM] range_analysis_pass_correct)
  \\ disch_then (qspecl_then [`fn`, `range_sound`,
    `\s:venom_state. dfg_sound (dfg_build_function fn) s.vs_vars /\
       (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
          vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
          u IN FDOM s.vs_vars)`,
    `\v inst. [assert_elim_inst v inst]`] mp_tac)
  \\ BETA_TAC >> DISCH_TAC
  \\ first_x_assum mp_tac >> impl_tac
  >- (rpt conj_tac
      >- metis_tac[range_transfer_sound]
      >- (mp_tac range_successor_obligation >>
          (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
          strip_tac >> first_assum ACCEPT_TAC)
      >- metis_tac[assert_elim_inst_simulates_proof]
      >- first_assum ACCEPT_TAC (* wf_function *)
      >- first_assum ACCEPT_TAC (* fn_inst_wf *)
      >- metis_tac[range_sound_state_equiv]
      >- metis_tac[dfg_sound_state_equiv, state_equiv_empty_vars_eq]
      >> rpt strip_tac >>
         fs[state_equiv_def, execution_equiv_def, lookup_var_def])
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  \\ impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
  \\ strip_tac
  >| [ (* Error case *)
       DISJ1_TAC >> metis_tac[]
     , (* Success case: compose framework result with clear_nops *)
       DISJ2_TAC >>
       irule lift_result_trans >>
       conj_tac >- (metis_tac[stateEquivPropsTheory.state_equiv_trans]) >>
       conj_tac >- (metis_tac[stateEquivPropsTheory.execution_equiv_trans]) >>
       qexists_tac `run_blocks fuel ctx
         (analysis_function_transform_widen NONE (range_analyze fn)
           (\v inst. [assert_elim_inst v inst]) fn) s` >>
       conj_tac >- (first_assum ACCEPT_TAC) >>
       simp_tac std_ss [GSYM stateEquivPropsTheory.result_equiv_is_lift_result] >>
       irule passSharedPropsTheory.clear_nops_function_correct >> simp[]
     ]
QED
