Theory cseAssignProps
Ancestors cseStageBindingProps passSharedProps cseWrapperProps
Libs cseReplayLib

(* Eligible singleton instructions change only their declared result.  The
   result-shape conclusion also excludes Abort/Halt/IntRet without assuming OK. *)
Theorem cse_singleton_result_shape:
 inst_wf inst /\ inst.inst_outputs = [x] /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ ~avail_nonidempotent inst.inst_opcode /\
 ~is_alloca_op inst.inst_opcode ==>
 (?e. step_inst n ctx inst s = Error e) \/
 (?v. step_inst n ctx inst s = OK (update_var x v s))
Proof
 strip_tac >>
 `inst.inst_opcode <> INVOKE` by
   (strip_tac >> gvs[availExprDefsTheory.avail_nonidempotent_def,
                    venomEffectsTheory.is_nonidempotent_def]) >>
 simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
 Cases_on `inst.inst_opcode` >>
 gvs[venomInstTheory.is_pseudo_def, venomInstTheory.is_terminator_def,
     availExprDefsTheory.avail_nonidempotent_def,
     venomEffectsTheory.is_nonidempotent_def, venomInstTheory.is_alloca_op_def] >>
 cseReplayLib.selected_base_tac >>
 qpat_x_assum `inst_wf inst` mp_tac >>
 pure_rewrite_tac[venomWfTheory.inst_wf_def] >> simp[] >> rpt strip_tac >>
 FIRST [irule exec_pure1_singleton_shape, irule exec_pure2_singleton_shape,
        irule exec_pure3_singleton_shape, irule exec_read0_singleton_shape,
        irule exec_read1_singleton_shape,
        (rpt (CASE_TAC >> gvs[]) >> metis_tac[])] >> simp[]
QED

Theorem cse_available_assign_replacement:
 wf_function fn /\ fn_inst_wf fn /\ cse_reachable_wf_ssa fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 events (CseExec n bb s) /\
 get_instruction bb s.vs_inst_idx = SOME inst /\
 inst_wf inst /\ inst_wf src /\ inst.inst_outputs = [x] /\ src.inst_outputs = [y] /\
 FLOOKUP (ae_lookup_inst fn bb.bb_label s.vs_inst_idx)
   (mk_expr (dfg_build_function fn) inst) = SOME xs /\ MEM src xs /\
 operand_ids_match
   (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
   (dfg_build_function fn) inst src ==>
 (?e. step_inst n ctx inst s = Error e) \/
 lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
   (step_inst n ctx inst s) (step_inst n ctx (mk_assign_inst inst (Var y)) s)
Proof
 strip_tac >>
 `MEM src (fn_insts fn) /\
  avail_source_birth (dfg_build_function fn)
    (mk_expr (dfg_build_function fn) inst) src src` by
   (irule cseSourcePropsTheory.cse_avail_source_provenance >>
    metis_tac[availExprDefsTheory.ae_lookup_inst_def]) >>
 `~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
  ~is_terminator inst.inst_opcode /\ ~avail_nonidempotent inst.inst_opcode` by
   (gvs[availExprProofsTheory.avail_source_birth_def] >>
    `inst.inst_opcode = src.inst_opcode` by
      metis_tac[cseReplayPropsTheory.mk_expr_root_inversion] >> simp[]) >>
 `~is_alloca_op inst.inst_opcode` by
   (drule_all cseHistoryPropsTheory.cse_prefix_exec_control >> strip_tac >>
    `MEM inst (fn_insts fn)` by
      (simp[venomInstTheory.fn_insts_def] >>
       irule venomInstTheory.fmp_fn_insts_blocks_intro >>
       gvs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
       metis_tac[venomExecPropsTheory.lookup_block_MEM, listTheory.EL_MEM]) >>
    gvs[listTheory.EVERY_MEM]) >>
 drule_all cse_singleton_result_shape >>
 disch_then (qspecl_then [`s`, `n`, `ctx`] mp_tac) >> strip_tac >> simp[] >>
 `cse_stage_binding fn (LENGTH (cse_canon_inputs (avail_analyze fn) fn))` by
   metis_tac[cse_stage_binding_all] >>
 `operand_ids_match
   (cse_stage_canon fn (LENGTH (cse_canon_inputs (avail_analyze fn) fn)))
   (dfg_build_function fn) inst src` by simp[cse_stage_canon_final] >>
 `lookup_var x (update_var x v s) = lookup_var y s` by
   (irule cse_stage_available_singleton_replay >> metis_tac[]) >>
 `lookup_var y s = SOME v` by
   gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
 `step_inst n ctx (mk_assign_inst inst (Var y)) s = OK (update_var x v s)` by
   (irule mk_assign_inst_correct >> simp[venomStateTheory.eval_operand_def]) >>
 simp[stateEquivTheory.lift_result_def, stateEquivPropsTheory.state_equiv_refl]
QED
