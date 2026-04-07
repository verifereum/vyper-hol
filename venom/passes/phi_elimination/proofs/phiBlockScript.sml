(*
 * PHI Elimination Block-Level Correctness
 *
 * Per-block simulation: transform_block preserves execution semantics
 * when vs_prev_bb is set (reachable non-entry blocks).
 *
 * Uses lift_result for compatibility with block_sim_function_pointwise_reachable.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMA:
 *   - phi_elim_block_sim   : Per-block simulation (guarded by prev_bb)
 *
 * HELPER THEOREMS (proven):
 *   - block_step_equiv           : Single step produces equivalent states
 *   - block_step_*_transform     : Halt/Abort/IntRet cases (identity)
 *   - step_inst_preserves_prev_bb: prev_bb preserved by non-terminators
 *   - block_step_preserves_prev_bb: block_step preserves prev_bb
 *
 * ============================================================================
 *)

Theory phiBlock
Ancestors
  phiWellFormed execEquivProps venomExecProofs venomExecSemantics venomState venomInst venomWf phiDefs phiOrigins phiTransform stateEquiv stateEquivProps list

(* ==========================================================================
   Instruction Step Lemmas
   ========================================================================== *)

Theorem step_inst_assign_eval:
  !inst out op s.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op] /\
    inst.inst_outputs = [out]
  ==>
    step_inst_base inst s =
      case eval_operand op s of
        SOME v => OK (update_var out v s)
      | NONE => Error "undefined operand"
Proof
  rw[step_inst_base_def]
QED

Theorem step_inst_phi_resolves_var_ok:
  !inst s s' src_var out prev.
    is_phi_inst inst /\
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var src_var) /\
    step_inst_base inst s = OK s'
  ==>
    ?v. lookup_var src_var s = SOME v /\ s' = update_var out v s
Proof
  rpt strip_tac >>
  fs[is_phi_inst_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, eval_operand_def] >>
  Cases_on `lookup_var src_var s` >> simp[]
QED

(* ==========================================================================
   Transform Instruction Correctness
   ========================================================================== *)

(* KEY LEMMA: Transform instruction correctness *)
Theorem transform_inst_correct:
  !dfg inst s s' origin prev_bb v.
    step_inst_base inst s = OK s' /\
    phi_single_origin dfg inst = SOME origin /\
    s.vs_prev_bb = SOME prev_bb /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v) /\
    dfg_lookup dfg v = SOME origin
  ==>
    ?s''. step_inst_base (transform_inst dfg inst) s = OK s'' /\
          state_equiv {} s' s''
Proof
  rpt strip_tac >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  `origin.inst_outputs = [v]` by metis_tac[dfg_lookup_single_output] >>
  fs[transform_inst_def, is_phi_inst_def] >>
  qexists_tac `s'` >>
  conj_tac >- (
    qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
    simp[step_inst_base_def, eval_operand_def] >>
    Cases_on `lookup_var v s` >> simp[] >>
    strip_tac >> fs[] >>
    Cases_on `inst.inst_outputs` >> fs[] >>
    Cases_on `t` >> fs[]
  ) >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Block Step Equivalence
   ========================================================================== *)

(* KEY LEMMA: Single step in block produces equivalent states *)
Theorem block_step_equiv:
  !dfg bb s s' is_term.
    block_step bb s = (OK s', is_term) /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       s.vs_prev_bb = SOME prev_bb /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup dfg v = SOME origin)
  ==>
    ?s''. block_step (transform_block dfg bb) s = (OK s'', is_term) /\
          state_equiv {} s' s''
Proof
  rpt strip_tac >>
  fs[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  rename1 `get_instruction bb _ = SOME curr_inst` >>
  imp_res_tac get_instruction_transform >>
  simp[] >>
  Cases_on `step_inst_base curr_inst s` >> fs[] >>
  simp[transform_inst_preserves_terminator] >>
  Cases_on `is_phi_inst curr_inst` >- (
    Cases_on `phi_single_origin dfg curr_inst` >- (
      imp_res_tac transform_inst_identity >> simp[state_equiv_refl]
    ) >>
    rename1 `phi_single_origin dfg curr_inst = SOME origin_inst` >>
    `phi_well_formed curr_inst.inst_operands` by metis_tac[] >>
    fs[is_phi_inst_def, step_inst_base_def] >>
    Cases_on `curr_inst.inst_outputs` >> fs[] >>
    Cases_on `t` >> fs[] >>
    rename1 `curr_inst.inst_outputs = [out_var]` >>
    Cases_on `s.vs_prev_bb` >> fs[] >>
    rename1 `s.vs_prev_bb = SOME prev_label` >>
    Cases_on `resolve_phi prev_label curr_inst.inst_operands` >> fs[] >>
    rename1 `resolve_phi _ _ = SOME resolved_op` >>
    Cases_on `eval_operand resolved_op s` >> fs[] >>
    `?var. resolved_op = Var var` by metis_tac[resolve_phi_well_formed] >>
    gvs[] >>
    (* Use the compatibility lookup assumption. *)
    first_x_assum (qspecl_then [`s.vs_inst_idx`, `curr_inst`, `origin_inst`, `var`] mp_tac) >>
    simp[] >> strip_tac >>
    `origin_inst.inst_outputs = [var]` by metis_tac[dfg_lookup_single_output] >>
    fs[transform_inst_def, eval_operand_def, step_inst_base_def] >>
    simp[state_equiv_refl]
  ) >>
  imp_res_tac transform_inst_non_phi >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Halt/Revert/Error Cases
   ========================================================================== *)

(* For Halt/Abort/IntRet cases, block_step on transformed block gives same result *)
Theorem block_step_nonOK_transform:
  !dfg bb s s' is_term.
    (block_step bb s = (Halt s', is_term) \/
     block_step bb s = (Abort a s', is_term) \/
     (?vs. block_step bb s = (IntRet vs s', is_term)))
  ==>
    block_step (transform_block dfg bb) s = block_step bb s
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  imp_res_tac get_instruction_transform >> fs[] >>
  gvs[AllCaseEqs()] >>
  `~is_phi_inst x` by (
    CCONTR_TAC >> fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
  ) >>
  imp_res_tac transform_inst_non_phi >> fs[]
QED

Theorem block_step_halt_transform:
  !dfg bb s s' is_term.
    block_step bb s = (Halt s', is_term) ==>
    block_step (transform_block dfg bb) s = (Halt s', is_term)
Proof
  metis_tac[block_step_nonOK_transform]
QED

Theorem block_step_abort_transform:
  !dfg bb s a s' is_term.
    block_step bb s = (Abort a s', is_term) ==>
    block_step (transform_block dfg bb) s = (Abort a s', is_term)
Proof
  metis_tac[block_step_nonOK_transform]
QED

Theorem block_step_intret_transform:
  !dfg bb s vals s' is_term.
    block_step bb s = (IntRet vals s', is_term) ==>
    block_step (transform_block dfg bb) s = (IntRet vals s', is_term)
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  imp_res_tac get_instruction_transform >> fs[] >>
  gvs[AllCaseEqs()] >>
  `~is_phi_inst x` by (
    CCONTR_TAC >> fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
  ) >>
  imp_res_tac transform_inst_non_phi >> fs[]
QED

(* ==========================================================================
   prev_bb Preservation
   ========================================================================== *)

(* Local version for step_inst_base (used by block_step_preserves_prev_bb).
   The general version for step_inst (covering INVOKE) is in venomExecProofsTheory. *)
Triviality step_inst_base_preserves_prev_bb:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  simp[exec_pure2_def, exec_pure1_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_ext_call_def, exec_delegatecall_def,
       exec_create_def, exec_alloca_def,
       extract_venom_result_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
  gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
      write_memory_with_expansion_def, mcopy_def, revert_state_def]
QED

Theorem block_step_preserves_prev_bb:
  !bb s s' is_term.
    block_step bb s = (OK s', is_term) /\
    ~is_term ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  gvs[AllCaseEqs()] >>
  drule_all step_inst_base_preserves_prev_bb >>
  simp[next_inst_def]
QED

(* ==========================================================================
   Per-Block Simulation (KEY THEOREM)

   This is the main block-level correctness theorem.
   Uses lift_result for direct integration with block_sim_function_pointwise_reachable.
   Guarded by vs_prev_bb <> NONE (satisfied for all reachable non-entry blocks).
   ========================================================================== *)

(* Helper: state_equiv {} implies equality *)
Theorem state_equiv_empty_eq[local]:
  !s1 s2. state_equiv {} s1 s2 ==> (s1 = s2)
Proof
  rw[state_equiv_def, execution_equiv_def,
     venom_state_component_equality] >>
  `FLOOKUP s1.vs_vars = FLOOKUP s2.vs_vars` by
    (simp[FUN_EQ_THM] >> fs[lookup_var_def]) >>
  fs[finite_mapTheory.FLOOKUP_EXT]
QED

(* Helper: phi_single_origin always gives an origin with singleton output *)
Theorem phi_single_origin_has_output[local]:
  !dfg inst origin.
    phi_single_origin dfg inst = SOME origin ==>
    ?v. origin.inst_outputs = [v] /\ dfg_lookup dfg v = SOME origin
Proof
  rw[phi_single_origin_def] >> gvs[AllCaseEqs()] >>
  `compute_origins dfg inst DELETE inst <> {}` by
    (strip_tac >> gvs[]) >>
  `CHOICE (compute_origins dfg inst DELETE inst) IN
   (compute_origins dfg inst DELETE inst)` by
    metis_tac[pred_setTheory.CHOICE_DEF] >>
  fs[pred_setTheory.IN_DELETE] >>
  drule_all compute_origins_non_self_in_dfg >> strip_tac >>
  metis_tac[dfg_lookup_single_output]
QED

(* When a PHI step succeeds, resolve_phi must have returned SOME *)
Triviality phi_step_ok_resolve:
  !inst s s' prev.
    is_phi_inst inst /\
    s.vs_prev_bb = SOME prev /\
    step_inst_base inst s = OK s' ==>
    ?op. resolve_phi prev inst.inst_operands = SOME op
Proof
  rw[is_phi_inst_def, step_inst_base_def] >>
  gvs[AllCaseEqs()]
QED

(* KEY HELPER: Per-step lift_result for PHI with single origin.
   Combines OK case (transform_inst_correct + state_equiv_empty_eq)
   and Error case (both sides error on same undefined variable).
   Factors out ALL per-step reasoning from the inductive proof. *)
Triviality phi_step_lift_result[local]:
  !dfg inst s origin prev src_var.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    s.vs_prev_bb = SOME prev /\
    phi_well_formed inst.inst_operands /\
    (!v. resolve_phi prev inst.inst_operands = SOME (Var v) ==>
         dfg_lookup dfg v = SOME origin) /\
    (!e. step_inst_base inst s = Error e ==>
         lookup_var src_var s = NONE)
  ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (step_inst_base inst s)
      (step_inst_base (transform_inst dfg inst) s)
Proof
  rpt strip_tac >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  Cases_on `step_inst_base inst s`
  >- ( (* OK case: use transform_inst_correct *)
    rename1 `_ = OK s'` >>
    `?op. resolve_phi prev inst.inst_operands = SOME op` by
      metis_tac[phi_step_ok_resolve] >>
    `?var. op = Var var` by metis_tac[resolve_phi_well_formed] >>
    gvs[] >>
    `dfg_lookup dfg var = SOME origin` by metis_tac[] >>
    `origin.inst_outputs = [var]` by metis_tac[dfg_lookup_single_output] >>
    gvs[] >>
    drule_all transform_inst_correct >> strip_tac >>
    drule state_equiv_empty_eq >> strip_tac >> gvs[] >>
    simp[lift_result_def, state_equiv_refl]
  )
  (* Halt/Abort/IntRet impossible for PHI *)
  >- (fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()])
  >- (fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()])
  >- (fs[is_phi_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()])
  >- ( (* Error case: original PHI errors, show transform also errors *)
    simp[lift_result_def] >>
    `lookup_var src_var s = NONE` by metis_tac[] >>
    `transform_inst dfg inst =
       inst with <| inst_opcode := ASSIGN;
                    inst_operands := [Var src_var] |>` by
      fs[is_phi_inst_def, transform_inst_def] >>
    pop_assum (fn th => REWRITE_TAC [th]) >>
    CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss())
      [step_inst_base_def, eval_operand_def])) >>
    Cases_on `inst.inst_outputs` >> simp[lift_result_def] >>
    Cases_on `t` >> simp[lift_result_def]
  )
QED

Theorem phi_elim_block_sim:
  !dfg bb fuel ctx s.
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb <> NONE /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup dfg v = SOME origin) /\
    (!inst origin src_var prev e s' fuel' ctx'.
       get_instruction bb s'.vs_inst_idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       origin.inst_outputs = [src_var] /\
       s'.vs_prev_bb = SOME prev /\
       step_inst fuel' ctx' inst s' = Error e ==>
       lookup_var src_var s' = NONE)
  ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_block fuel ctx bb s)
      (run_block fuel ctx (transform_block dfg bb) s)
Proof
  rpt gen_tac >> strip_tac >>
  ntac 4 (pop_assum mp_tac) >> pop_assum kall_tac >>
  qid_spec_tac `s` >> qid_spec_tac `bb` >>
  qid_spec_tac `ctx` >> qid_spec_tac `fuel` >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV
    (SIMP_CONV (srw_ss()) [Once run_block_def]))) >>
  CONV_TAC (RAND_CONV
    (SIMP_CONV (srw_ss()) [Once run_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- (
    `get_instruction (transform_block dfg bb) s.vs_inst_idx = NONE` by
      gvs[get_instruction_def, transform_block_def] >>
    simp[lift_result_def]) >>
  rename1 `_ = SOME inst` >>
  imp_res_tac get_instruction_transform >> gvs[] >>
  (* Case split: does phi_single_origin produce an origin? *)
  Cases_on `phi_single_origin dfg inst`
  >- (
    (* NONE: transform is identity, both sides use same step_inst *)
    `transform_inst dfg inst = inst` by metis_tac[transform_inst_identity] >>
    pop_assum SUBST_ALL_TAC >>
    Cases_on `step_inst fuel ctx inst s` >>
    simp[lift_result_def, execution_equiv_refl] >>
    (* Only OK case remains; split on terminator *)
    IF_CASES_TAC >> simp[]
    >- ( (* terminator: both sides identical *)
      IF_CASES_TAC >> simp[lift_result_def, state_equiv_refl,
                           execution_equiv_refl])
    >- ( (* non-terminator: apply IH *)
      first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
      disch_then (fn th =>
        mp_tac th >> impl_tac >- (
          drule_all step_inst_preserves_prev_bb >> simp[]) >>
        impl_tac >- metis_tac[] >>
        impl_tac >- metis_tac[] >>
        impl_tac >- metis_tac[] >>
        simp[]))
  )
  >- ( (* SOME case *)
    rename1 `phi_single_origin dfg inst = SOME origin` >>
    `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
    `?src_var. origin.inst_outputs = [src_var] /\
               dfg_lookup dfg src_var = SOME origin` by
      metis_tac[phi_single_origin_has_output] >>
    `phi_well_formed inst.inst_operands` by metis_tac[] >>
    Cases_on `s.vs_prev_bb` >- fs[] >>
    rename1 `s.vs_prev_bb = SOME prev` >>
    `~is_terminator inst.inst_opcode` by fs[is_phi_inst_def, is_terminator_def] >>
    `inst.inst_opcode <> INVOKE` by fs[is_phi_inst_def] >>
    `step_inst fuel ctx inst s = step_inst_base inst s` by
      metis_tac[step_inst_non_invoke] >>
    `(transform_inst dfg inst).inst_opcode <> INVOKE` by
      fs[is_phi_inst_def, transform_inst_def] >>
    `step_inst fuel ctx (transform_inst dfg inst) s =
     step_inst_base (transform_inst dfg inst) s` by
      metis_tac[step_inst_non_invoke] >>
    qpat_x_assum `step_inst fuel ctx inst s = _`
      (fn th => REWRITE_TAC [th] >> ASSUME_TAC th) >>
    qpat_x_assum `step_inst fuel ctx (transform_inst dfg inst) s = _`
      (fn th => REWRITE_TAC [th] >> ASSUME_TAC th) >>
    `lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
       (step_inst_base inst s) (step_inst_base (transform_inst dfg inst) s)` by (
      irule phi_step_lift_result >> simp[] >>
      conj_tac >- (
        rpt strip_tac >>
        `step_inst fuel ctx inst s = Error e` by
          metis_tac[step_inst_non_invoke] >>
        first_x_assum (qspecl_then
          [`inst`, `origin`, `src_var`, `prev`, `e`, `s`, `fuel`, `ctx`]
          mp_tac) >> simp[]
      ) >>
      metis_tac[]
    ) >>
    (* Case split on original step result *)
    Cases_on `step_inst_base inst s`
    (* Handle ALL 5 result cases together for debuggability *)
    >> (
      (* For Halt/Abort/IntRet: contradiction from is_phi_inst *)
      TRY (`inst.inst_opcode = PHI` by fs[is_phi_inst_def] >>
           simp[Once step_inst_base_def] >> gvs[AllCaseEqs()] >> NO_TAC) >>
      (* For Error: resolve second side via lift_result assumption *)
      TRY (qpat_x_assum `lift_result _ _ _ (step_inst_base _ _)` mp_tac >>
           Cases_on `step_inst_base (transform_inst dfg inst) s` >>
           simp[lift_result_def, execution_equiv_refl] >> NO_TAC) >>
      (* OK case: derive both sides return OK with same state *)
      rename1 `step_inst_base inst s = OK s_orig` >>
      `step_inst_base (transform_inst dfg inst) s = OK s_orig` by (
        qpat_x_assum `lift_result _ _ (OK _) _` mp_tac >>
        Cases_on `step_inst_base (transform_inst dfg inst) s` >>
        simp[lift_result_def] >>
        strip_tac >> imp_res_tac state_equiv_empty_eq >> fs[]) >>
      `~is_terminator (transform_inst dfg inst).inst_opcode` by
        fs[transform_inst_def, is_phi_inst_def, is_terminator_def] >>
      `s_orig.vs_prev_bb <> NONE` by
        (imp_res_tac step_inst_preserves_prev_bb >> fs[]) >>
      simp[] >>
      first_x_assum (qspec_then `s_orig` mp_tac) >> simp[] >>
      disch_then irule >> metis_tac[]
    )
  )
QED

