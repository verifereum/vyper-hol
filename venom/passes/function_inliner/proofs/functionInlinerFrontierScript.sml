(* Allocation frontier sidecar: independent of the live storage abstraction. *)
Theory functionInlinerFrontier
Ancestors
  functionInlinerLiveInvariant functionInlinerOrigin functionInlinerContract
  venomMemProofs venomExecProofs venomExecSemantics venomState venomInst stateFrame
  functionInlinerFrame list

Definition inline_frontier_result_def:
  (inline_frontier_result n (OK s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (Halt s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (Abort a s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (IntRet ir s) <=> s.vs_alloca_next = n) /\
  (inline_frontier_result n (Error e) <=> T)
End

Definition inline_frontier_instruction_def:
  inline_frontier_instruction inst <=> inst.inst_opcode <> ALLOCA
End

Definition inline_frontier_function_def:
  inline_frontier_function fn <=>
    EVERY (\bb. EVERY inline_frontier_instruction bb.bb_instructions) fn.fn_blocks
End

Definition inline_frontier_context_def:
  inline_frontier_context C <=> EVERY inline_frontier_function C.ctx_functions
End

Theorem inline_frontier_update_var[simp]:
  (update_var x w s).vs_alloca_next = s.vs_alloca_next
Proof simp[update_var_def]
QED

Theorem inline_frontier_assignments[simp]:
  !pairs s. (FOLDL (\s (x,w). update_var x w s) s pairs).vs_alloca_next =
    s.vs_alloca_next
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[]
QED

Theorem inline_frontier_bind_outputs:
  bind_outputs outs vals s = SOME t ==> t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[]
QED

Theorem inline_frontier_merge[simp]:
  (merge_callee_state s t).vs_alloca_next = s.vs_alloca_next
Proof simp[merge_callee_state_def]
QED

Theorem inline_frontier_adopt[simp]:
  (adopt_return_fmp ir s).vs_alloca_next = s.vs_alloca_next
Proof Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem inline_frontier_setup:
  setup_callee fn args s = SOME t ==> t.vs_alloca_next = s.vs_alloca_next
Proof simp[setup_callee_def] >> strip_tac >> gvs[]
QED

Theorem inline_frontier_base:
  inline_frontier_instruction inst /\ inst.inst_opcode <> INVOKE ==>
  inline_frontier_result s.vs_alloca_next (step_inst_base inst s)
Proof
  strip_tac >> Cases_on `step_inst_base inst s` >>
  gvs[inline_frontier_result_def, inline_frontier_instruction_def] >>
  metis_tac[step_inst_base_preserves_alloca_next]
QED

Theorem inline_frontier_setup_compare:
  inline_shared_frame s = inline_shared_frame t /\
  s.vs_alloca_next = t.vs_alloca_next /\
  fn.fn_blocks <> [] /\ gn.fn_blocks <> [] /\
  (HD fn.fn_blocks).bb_label = (HD gn.fn_blocks).bb_label /\
  ~s.vs_halted /\ ~t.vs_halted ==>
  setup_callee fn args s = setup_callee gn args t
Proof
  simp[inline_shared_frame_def, execution_frame_def,
       venom_state_component_equality] >>
  rpt strip_tac >>
  simp[setup_callee_def, NULL_EQ, venom_state_component_equality]
QED

Theorem inline_frontier_phis:
  eval_phis s insts = OK t ==> t.vs_alloca_next = s.vs_alloca_next
Proof metis_tac[eval_phis_preserves_alloca_fields]
QED

Theorem inline_frontier_evaluation:
  (!fuel C inst s. inline_frontier_context C /\ inline_frontier_instruction inst ==>
    inline_frontier_result s.vs_alloca_next (step_inst fuel C inst s)) /\
  (!fuel C bb s. inline_frontier_context C /\
    EVERY inline_frontier_instruction bb.bb_instructions ==>
    inline_frontier_result s.vs_alloca_next (exec_block fuel C bb s)) /\
  (!fuel C fn s. inline_frontier_context C /\ inline_frontier_function fn ==>
    inline_frontier_result s.vs_alloca_next (run_blocks fuel C fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac >> rpt strip_tac
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (once_rewrite_tac[step_inst_def] >> simp[] >>
          rpt (BasicProvers.TOP_CASE_TAC >> simp[inline_frontier_result_def]) >>
          rename1 `lookup_function _ C.ctx_functions = SOME callee` >>
          `inline_frontier_function callee` by
            (gvs[inline_frontier_context_def, EVERY_MEM] >>
             metis_tac[lookup_function_MEM]) >>
          gvs[inline_frontier_result_def] >>
          metis_tac[inline_frontier_setup, inline_frontier_bind_outputs,
                    inline_frontier_merge, inline_frontier_adopt]) >>
      simp[step_inst_non_invoke] >> irule inline_frontier_base >> simp[])
  >- (once_rewrite_tac[exec_block_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >>
      simp[inline_frontier_result_def] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `inline_frontier_instruction inst` by
        (gvs[get_instruction_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
      `inline_frontier_result s.vs_alloca_next (step_inst fuel C inst s)` by
        metis_tac[] >>
      Cases_on `step_inst fuel C inst s` >>
      gvs[inline_frontier_result_def] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[inline_frontier_result_def] >>
      Cases_on `v.vs_halted` >> simp[inline_frontier_result_def] >>
      metis_tac[])
  >> once_rewrite_tac[run_blocks_def] >> Cases_on `fuel` >>
  simp[inline_frontier_result_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[inline_frontier_result_def] >> rename1 `lookup_block _ _ = SOME bb` >>
  `EVERY inline_frontier_instruction bb.bb_instructions` by
    (gvs[inline_frontier_function_def, EVERY_MEM] >>
     metis_tac[lookup_block_MEM]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (simp[] >>
      `s'.vs_alloca_next = s.vs_alloca_next` by metis_tac[inline_frontier_phis] >>
      `inline_frontier_result s.vs_alloca_next
         (exec_block n C bb (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
        (gvs[] >> metis_tac[]) >>
      Cases_on `exec_block n C bb (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[inline_frontier_result_def] >>
      Cases_on `v.vs_halted` >> simp[inline_frontier_result_def] >> metis_tac[]) >>
  simp[inline_frontier_result_def]
QED

Theorem inline_frontier_input:
  inliner_input_ok C ==> inline_frontier_context C
Proof
  simp[inline_frontier_context_def, inline_frontier_function_def, EVERY_MEM,
       inline_frontier_instruction_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  fs[inliner_input_ok_def, EVERY_MEM] >>
  metis_tac[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff]
QED
