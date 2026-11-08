(*
 * Dead Store Elimination — Correctness Statement
 *
 * Preconditions: wf_function + ssa_form, and a state invariant safe_inv that
 *   holds at the start, survives every step of fn, and implies alloca safety,
 *   soundness of fn's base-pointer analysis, and accesses staying in their
 *   own alloca (see deadStoreElimProofsScript)
 * Conclusion includes Error disjunct: original execution may error while
 *   DSE-transformed succeeds (e.g. undefined operand in dead store).
 * See deadStoreElimProofsScript.sml for counterexamples and explanation.
 *
 * Previous theorems (alloca_inv + bp_ptrs_bounded) were FALSE — see
 *   FALSE1-5 theorems in deadStoreElimProofsScript.sml.
 *)

Theory deadStoreElimCorrectness
Ancestors
  deadStoreElimProofs deadStoreElimComposition deadStoreElimCertificate
  decoratedExecution deadStoreElimStructure deadStoreElimEquiv venomWf
  basePtrProps While deadStoreElimDefs passSharedDefs passSharedProps
  venomInst passSimulationProps allocaRemapDefs pointerConfinedDefs

(* ===== Obligations ===== *)

(* OWHILE preserves wf/ssa via WhileTheory.OWHILE_INV_IND *)

val owhile_wf = OWHILE_INV_IND
  |> INST_TYPE [alpha |-> ``:ir_function``]
  |> INST [``P:ir_function -> bool`` |-> ``wf_function``];

val owhile_wf_ssa = OWHILE_INV_IND
  |> INST_TYPE [alpha |-> ``:ir_function``]
  |> INST [``P:ir_function -> bool`` |->
     ``\fn'. wf_function fn' /\ ssa_form fn'``]
  |> SIMP_RULE (srw_ss()) [];

Triviality dse_iterate_preserves_wf:
  !analysis_fn space fn fn'.
    dse_iterate analysis_fn space fn = SOME fn' /\
    wf_function fn ==>
    wf_function fn'
Proof
  rpt strip_tac >> fs[dse_iterate_def] >>
  drule_then irule owhile_wf >>
  first_assum (irule_at Any) >> rpt strip_tac >>
  BETA_TAC >> irule dse_single_pass_preserves_wf >> simp[]
QED

Triviality dse_iterate_preserves_ssa:
  !analysis_fn space fn fn'.
    dse_iterate analysis_fn space fn = SOME fn' /\
    wf_function fn /\ ssa_form fn ==>
    wf_function fn' /\ ssa_form fn'
Proof
  rpt gen_tac >> strip_tac >> fs[dse_iterate_def] >>
  drule_then irule owhile_wf_ssa >>
  qpat_x_assum `OWHILE _ _ _ = _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> BETA_TAC >>
  metis_tac[dse_single_pass_preserves_wf, dse_single_pass_preserves_ssa]
QED

(* dse_function_space preserves wf/ssa *)

Triviality dse_function_space_preserves_wf:
  !analysis_fn space fn.
    wf_function fn ==> wf_function (dse_function_space analysis_fn space fn)
Proof
  rw[dse_function_space_def] >>
  CASE_TAC >> simp[] >>
  irule clear_nops_function_preserves_wf >>
  TRY (irule dse_iterate_preserves_wf >> metis_tac[]) >>
  simp[]
QED

Triviality dse_function_space_preserves_ssa:
  !analysis_fn space fn.
    wf_function fn /\ ssa_form fn ==>
    wf_function (dse_function_space analysis_fn space fn) /\
    ssa_form (dse_function_space analysis_fn space fn)
Proof
  rpt gen_tac >> strip_tac >>
  simp[dse_function_space_def] >>
  CASE_TAC
  >- ((* NONE *)
      metis_tac[clear_nops_function_preserves_wf,
                clear_nops_function_preserves_ssa])
  >- ((* SOME x *)
      drule dse_iterate_preserves_ssa >> simp[] >> strip_tac >>
      metis_tac[clear_nops_function_preserves_wf,
                clear_nops_function_preserves_ssa])
QED

(* ===== Obligations ===== *)

Theorem dse_preserves_wf_function:
  ∀analysis_fn fn. wf_function fn ⇒ wf_function (dse_function analysis_fn fn)
Proof
  rw[dse_function_def] >>
  ntac 3 (irule dse_function_space_preserves_wf >> simp[]) >>
  simp[]
QED

Theorem dse_preserves_ssa_form:
  ∀analysis_fn fn. wf_function fn ∧ ssa_form fn ⇒
    ssa_form (dse_function analysis_fn fn)
Proof
  rw[dse_function_def] >>
  `wf_function (dse_function_space analysis_fn AddrSp_Memory fn) /\
   ssa_form (dse_function_space analysis_fn AddrSp_Memory fn)` by
    (irule dse_function_space_preserves_ssa >> simp[]) >>
  `wf_function (dse_function_space analysis_fn AddrSp_Storage
     (dse_function_space analysis_fn AddrSp_Memory fn)) /\
   ssa_form (dse_function_space analysis_fn AddrSp_Storage
     (dse_function_space analysis_fn AddrSp_Memory fn))` by
    (irule dse_function_space_preserves_ssa >> simp[]) >>
  drule_all dse_function_space_preserves_ssa >>
  simp[]
QED

Theorem dse_function_space_correct:
  !analysis_fn space fuel ctx fn s safe_inv.
    wf_function fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_call_ctx.cc_static /\ safe_inv s /\
    (!bb s0 s1.
       lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
       s0.vs_inst_idx = 0 /\ safe_inv s0 /\
       eval_phis s0 bb.bb_instructions = OK s1 ==>
       safe_inv (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
    (!bb inst fuel' s0 s1.
       lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s0.vs_inst_idx = SOME inst /\ safe_inv s0 /\
       step_inst fuel' ctx inst s0 = OK s1 ==>
       safe_inv (if is_terminator inst.inst_opcode then s1
                 else s1 with vs_inst_idx := SUC s0.vs_inst_idx)) /\
    (!s0. safe_inv s0 ==>
       alloca_inv s0 /\
       (!aid base sz. FLOOKUP s0.vs_allocas aid = SOME (base, sz) ==>
                      base + sz < dimword (:256)) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s0 /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s0 /\
       (!bb inst.
          lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb s0.vs_inst_idx = SOME inst ==>
          bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s0)) /\
    (!fn'. all_dead_stores (analysis_fn space fn')
             (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
             space fn') ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?e. run_blocks fuel ctx fn s = Error e`
  >- simp[] >> disj2_tac >>
  `dse_run_certificate fn fuel ctx s (run_blocks fuel ctx fn s)` by
    (irule dse_certificate_initial >> simp[] >>
     reverse conj_tac >- metis_tac[] >>
     qexists_tac `safe_inv` >> simp[] >> metis_tac[]) >>
  drule_all dse_function_space_certificate >> strip_tac >>
  fs[dse_run_certificate_def] >>
  drule_all decorated_run_erase >> strip_tac >> simp[]
QED

Theorem dse_function_correct:
  !analysis_fn fuel ctx fn s safe_inv.
    wf_function fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_call_ctx.cc_static /\ safe_inv s /\
    (!bb s0 s1.
       lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
       s0.vs_inst_idx = 0 /\ safe_inv s0 /\
       eval_phis s0 bb.bb_instructions = OK s1 ==>
       safe_inv (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
    (!bb inst fuel' s0 s1.
       lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s0.vs_inst_idx = SOME inst /\ safe_inv s0 /\
       step_inst fuel' ctx inst s0 = OK s1 ==>
       safe_inv (if is_terminator inst.inst_opcode then s1
                 else s1 with vs_inst_idx := SUC s0.vs_inst_idx)) /\
    (!s0. safe_inv s0 ==>
       alloca_inv s0 /\
       (!aid base sz. FLOOKUP s0.vs_allocas aid = SOME (base, sz) ==>
                      base + sz < dimword (:256)) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s0 /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s0 /\
       (!bb inst.
          lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb s0.vs_inst_idx = SOME inst ==>
          bp_accesses_in_own_alloca (bp_analyze (cfg_analyze fn) fn) inst s0)) /\
    (!space fn'.
      all_dead_stores (analysis_fn space fn')
        (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
        space fn') ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function analysis_fn fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?e. run_blocks fuel ctx fn s = Error e`
  >- simp[] >> disj2_tac >>
  `dse_run_certificate fn fuel ctx s (run_blocks fuel ctx fn s)` by
    (irule dse_certificate_initial >> simp[] >>
     reverse conj_tac >- metis_tac[] >>
     qexists_tac `safe_inv` >> simp[] >> metis_tac[]) >>
  drule_all dse_function_certificate >> strip_tac >>
  fs[dse_run_certificate_def] >>
  drule_all decorated_run_erase >> strip_tac >> simp[]
QED
