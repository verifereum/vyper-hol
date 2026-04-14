(*
 * Concretize Memory Locations — Correctness Statement
 *
 * Three components:
 * 1. Allocator soundness: non-overlapping for simultaneously-live allocas.
 * 2. Liveness + allocator: compute_alloc_map satisfies live_non_overlapping.
 * 3. Simulation: given live_non_overlapping + memory safety + pointer
 *    confinement, the transformed program preserves semantics under
 *    the liveness-aware concretize_rel.
 *)

Theory concretizeMemLocCorrectness
Ancestors
  concretizeMemLocDefs concretizeMemLocProofs
  passSimulationProps passSharedDefs passSharedProps
  allocaRemapDefs pointerConfinedDefs
  venomExecSemantics venomMemDefs venomInst

Theorem concretize_function_correct:
  !amap fn livesets init fuel ctx s1 s2.
    venom_wf ctx /\ fn_inst_wf fn /\ ssa_form fn /\
    fn_inst_ids_distinct fn /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    live_non_overlapping livesets amap fn /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MSIZE) bb.bb_instructions)
      fn.fn_blocks /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (run_blocks fuel ctx fn s1)
        (run_blocks fuel ctx (concretize_function amap fn) s2)
Proof
  ACCEPT_TAC concretize_function_correct_proof
QED

(* ===== concretize_inst structural properties ===== *)

Triviality ci_preserves_id:
  !amap inst. (concretize_inst amap inst).inst_id = inst.inst_id
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> simp[mk_nop_inst_def, mk_assign_inst_def]
QED

Triviality ci_terminator_identity:
  !amap inst. is_terminator inst.inst_opcode ==>
              concretize_inst amap inst = inst
Proof
  simp[concretize_inst_def] >> rpt strip_tac >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> fs[is_alloca_op_def, is_terminator_def]) >>
  simp[]
QED

Triviality ci_non_term:
  !amap inst. ~is_terminator inst.inst_opcode ==>
              ~is_terminator (concretize_inst amap inst).inst_opcode
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> gvs[mk_nop_inst_def, mk_assign_inst_def, is_terminator_def]
QED

Triviality ci_phi:
  !amap inst. inst.inst_opcode = PHI ==>
              (concretize_inst amap inst).inst_opcode = PHI
Proof
  simp[concretize_inst_def, is_alloca_op_def]
QED

Triviality ci_non_phi:
  !amap inst. inst.inst_opcode <> PHI ==>
              (concretize_inst amap inst).inst_opcode <> PHI
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> gvs[mk_nop_inst_def, mk_assign_inst_def]
QED

Triviality ci_outputs:
  !amap inst. inst.inst_outputs = (concretize_inst amap inst).inst_outputs \/
              (concretize_inst amap inst).inst_outputs = []
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> simp[mk_nop_inst_def, mk_assign_inst_def]
QED

(* ===== Obligations ===== *)

Theorem concretize_preserves_wf_function:
  ∀amap fn. wf_function fn ⇒ wf_function (concretize_function amap fn)
Proof
  rpt strip_tac >> simp[concretize_function_def] >>
  irule clear_nops_function_preserves_wf >>
  irule map_transform_preserves_wf >>
  simp[ci_preserves_id, ci_terminator_identity, ci_non_term, ci_phi, ci_non_phi]
QED

Theorem concretize_preserves_ssa_form:
  ∀amap fn. wf_function fn ∧ ssa_form fn ⇒ ssa_form (concretize_function amap fn)
Proof
  rpt strip_tac >> simp[concretize_function_def] >>
  irule clear_nops_function_preserves_ssa >>
  irule map_transform_preserves_ssa >>
  simp[ci_preserves_id, ci_outputs] >>
  irule map_transform_preserves_wf >>
  simp[ci_preserves_id, ci_terminator_identity, ci_non_term, ci_phi, ci_non_phi]
QED
