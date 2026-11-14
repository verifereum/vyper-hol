(* Acceptance belongs to the logged round, not the original source. *)
Theory readonlyInvokeCopyFwdHistoryClosure
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdProtectionSelected
  readonlyInvokeCopyFwdPlan internalReturnCopyFwdPlan invokeCopyFwdCommonDefs
  occurrenceOrigin o1LowerDloadClosure ptrDiscipline list pred_set

Theorem ricf_function_edit_pointer_instruction:
  ricf_function_edit original round /\ MEM inst (fn_insts original) /\
  is_pointer_preserving_op inst.inst_opcode ==>
  MEM inst (fn_insts round)
Proof
  strip_tac >> drule ricf_function_edit_insts >>
  strip_tac >>
  `?other. MEM other (fn_insts round) /\ ricf_inst_edit inst other` by
    metis_tac[LIST_REL_MEM_IMP] >>
  `inst.inst_opcode <> MCOPY /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >>
     gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def]) >>
  gvs[ricf_inst_edit_def]
QED

Theorem ricf_located_event_destination_pointer_closure:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] ==>
  pointer_derived_vars original {icf_assign_root (dfg_build_function original) {} dst}
    SUBSET {v | ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v}
Proof
  strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule_all ricf_function_trace_edit >> strip_tac >>
  drule_all ricf_function_trace_assign_root >> strip_tac >>
  drule_all ricf_function_trace_collect_aliases >> strip_tac >>
  gvs[] >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  `(ricf_event_copy e current).inst_operands = [Var dst;src;sz]` by metis_tac[] >>
  irule pointer_derived_vars_least >> simp[ircf_alias_refl] >>
  rpt strip_tac >>
  `MEM inst (fn_insts round)` by metis_tac[ricf_function_edit_pointer_instruction] >>
  `?pos. pos < LENGTH inst.inst_operands /\
     EL pos inst.inst_operands = Var u` by metis_tac[MEM_EL] >>
  `ircf_alias round (icf_assign_root (dfg_build_function round) {} dst) u` by
    (fs[icf_collect_aliases_ircf_alias, EXTENSION] >> metis_tac[]) >>
  drule_all ricf_event_alias_use_accepted >>
  simp[icf_is_assign_output_use_def] >> strip_tac
  >- metis_tac[ircf_assign_pointer_alias]
  >- gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def]
  >> gvs[pointerConfinedDefsTheory.is_pointer_preserving_op_def]
QED

Theorem ricf_located_event_destination_occurrence_operand:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  fn_inst_wf original /\ fn_inst_ids_distinct original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands = [Var dst;src;sz] /\
  occurrence_syntax_origin original a H /\ MEM ai (fn_insts original) /\
  ai.inst_opcode = ALLOCA /\
  ai.inst_outputs = [icf_assign_root (dfg_build_function original) {} dst] /\
  op_prov H op = SOME (a,ai.inst_id) ==>
  ?v. op = Var v /\
    ircf_alias original (icf_assign_root (dfg_build_function original) {} dst) v
Proof
  strip_tac >> Cases_on `op` >> gvs[op_prov_def] >>
  drule_all occurrence_syntax_origin_planned_root >> strip_tac >>
  drule_all ricf_located_event_destination_pointer_closure >>
  simp[SUBSET_DEF]
QED
