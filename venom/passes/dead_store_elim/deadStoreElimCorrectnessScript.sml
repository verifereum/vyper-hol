(*
 * Dead Store Elimination — Correctness Statement
 *
 * The corrected theorems are in deadStoreElimProofsScript.sml:
 *   dse_function_space_correct_proof (cheated — proof in progress)
 *   dse_function_correct_proof (cheated — proof in progress)
 * Both add bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s to
 * prevent cross-allocation pointer arithmetic.
 *
 * The ORIGINAL frozen theorems are FALSE (counterexamples in
 * deadStoreElimProofsScript.sml, _FALSE theorems).
 *
 * The wf/ssa preservation theorems below remain valid.
 *)

Theory deadStoreElimCorrectness
Ancestors
  deadStoreElimProofs venomWf basePtrProps While
  deadStoreElimDefs passSharedDefs passSharedProps venomInst
  passSimulationProps

(* ===== Obligations ===== *)

(* dse_inst properties *)


(* Bridge lemmas: certain opcode classes are disjoint from is_memory_def_opcode.
   This avoids expanding write_effects_def (91 clauses) in every di_* proof. *)

Triviality terminator_not_memory_def:
  !space op. is_terminator op ==> ~is_memory_def_opcode space op
Proof
  Cases_on `op` >> simp[is_terminator_def, is_memory_def_opcode_def] >>
  Cases_on `space` >> EVAL_TAC
QED

Triviality phi_not_memory_def:
  !space. ~is_memory_def_opcode space PHI
Proof
  Cases_on `space` >> EVAL_TAC
QED

(* dse_inst either returns inst unchanged (guard false) or mk_nop_inst inst (guard true).
   All 6 di_* properties follow from this + the bridge lemmas above. *)

Triviality di_preserves_id:
  !dead_ids space inst. (dse_inst dead_ids space inst).inst_id = inst.inst_id
Proof
  rw[dse_inst_def] >> rpt CASE_TAC >> simp[mk_nop_inst_def]
QED

Triviality di_terminator_identity:
  !dead_ids space inst. is_terminator inst.inst_opcode ==>
    dse_inst dead_ids space inst = inst
Proof
  rpt strip_tac >> simp[dse_inst_def] >>
  imp_res_tac terminator_not_memory_def >> simp[]
QED

Triviality di_non_term:
  !dead_ids space inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (dse_inst dead_ids space inst).inst_opcode
Proof
  rw[dse_inst_def] >>
  rpt CASE_TAC >> gvs[mk_nop_inst_def, is_terminator_def]
QED

Triviality di_phi:
  !dead_ids space inst. inst.inst_opcode = PHI ==>
    (dse_inst dead_ids space inst).inst_opcode = PHI
Proof
  rpt strip_tac >> simp[dse_inst_def, phi_not_memory_def]
QED

Triviality di_non_phi:
  !dead_ids space inst. inst.inst_opcode <> PHI ==>
    (dse_inst dead_ids space inst).inst_opcode <> PHI
Proof
  rw[dse_inst_def] >>
  rpt CASE_TAC >> gvs[mk_nop_inst_def]
QED

Triviality di_outputs:
  !dead_ids space inst.
    inst.inst_outputs = (dse_inst dead_ids space inst).inst_outputs \/
    (dse_inst dead_ids space inst).inst_outputs = []
Proof
  rw[dse_inst_def] >>
  rpt CASE_TAC >> simp[mk_nop_inst_def]
QED

(* dse_single_pass preserves wf/ssa *)

Triviality dse_single_pass_preserves_wf:
  !dead_ids space fn. wf_function fn ==>
    wf_function (dse_single_pass dead_ids space fn)
Proof
  rw[dse_single_pass_def] >>
  irule map_transform_preserves_wf >>
  simp[di_preserves_id, di_terminator_identity, di_non_term, di_phi, di_non_phi]
QED

Triviality dse_single_pass_preserves_ssa:
  !dead_ids space fn. wf_function fn /\ ssa_form fn ==>
    wf_function (dse_single_pass dead_ids space fn) /\
    ssa_form (dse_single_pass dead_ids space fn)
Proof
  rpt strip_tac >> simp[dse_single_pass_def]
  >- (irule map_transform_preserves_wf >>
      simp[di_preserves_id, di_terminator_identity,
           di_non_term, di_phi, di_non_phi])
  >- (irule map_transform_preserves_ssa >>
      simp[di_preserves_id, di_outputs] >>
      irule map_transform_preserves_wf >>
      simp[di_preserves_id, di_terminator_identity,
           di_non_term, di_phi, di_non_phi])
QED

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
