(* The O1 pipeline keeps a leaf entry function's opcode absences: when the
 * entry function has no INVOKE, pruning keeps only it, and no O1 pass
 * introduces a RETURNDATACOPY or an INVOKE.
 * TOP-LEVEL: o1_pipeline_leaf_entry_no_returndatacopy (used by
 * deploy_frame_gas_sufficient).
 *)
Theory o1OpcodeAbsence
Ancestors
  o1PipelineCorrect venomPassDispatcherProps fcgPruning fcgDefs venomInst
  o1DftOpcodePreservation o1CfgOpcodePreservation o1SimpleStructuralOpcodes
  o1OpcodePassPreservation
  o1OpcodeRunnerPreservation o1LeafPruning
  venomPipelineDriver venomPassSchedule venomPipelineRunner venomCompilerWf
  venomWf list ctxLookupAgreeHelpers

Theorem execute_pre_walk_leaf_opcodes[local]:
  MEM (PS_MapFunctions pass) o1_pipeline_spec.ps_pre_walk_stages /\
  execute_configured_fn_pass rp pass u s f = SOME out /\
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (fn_insts out.fpo_function)
Proof
  simp[o1_pipeline_spec_def, EVERY_MEM] >>
  metis_tac[execute_o1_pre_walk_opcode_absence]
QED

Theorem o1_pipeline_leaf_entry_no_returndatacopy:
  !rpolicy unit out efn.
    o1_pipeline rpolicy unit = SOME out /\
    unit.cu_context.ctx_entry = SOME efn.fn_name /\
    lookup_function efn.fn_name unit.cu_context.ctx_functions = SOME efn /\
    (!inst. MEM inst (fn_insts efn) ==>
            inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> INVOKE)
    ==>
    !fn inst. MEM fn out.po_unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) ==>
              inst.inst_opcode <> RETURNDATACOPY
Proof
  rpt gen_tac >> strip_tac >>
  gvs[o1PipelineCorrectTheory.o1_pipeline_def,
      run_venom_pipeline_def, o1_pipeline_spec_def,
      AllCaseEqs()] >>
  qpat_x_assum `run_pipeline_stages _ [] _ _ = _` mp_tac >>
  simp[run_pipeline_stages_def] >> strip_tac >> gvs[] >>
  `ctx_wf unit.cu_context` by fs[unit_wf_def, venom_wf_def] >>
  `ctx_wf pre_unit.cu_context` by
    metis_tac[run_pipeline_stages_ctx_wf] >>
  `pre_unit.cu_context.ctx_entry = SOME efn.fn_name` by
    metis_tac[run_pipeline_stages_entry] >>
  drule_at (Pat `run_pipeline_stages _ _ _ _ = _`)
    (Q.INST [`P` |-> `\op. op <> RETURNDATACOPY /\ op <> INVOKE`]
      run_pipeline_stages_lookup_opcodes) >>
  disch_then (qspecl_then [`efn.fn_name`, `efn`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- metis_tac[SRULE [o1_pipeline_spec_def] execute_pre_walk_leaf_opcodes] >>
      simp[EVERY_MEM]) >>
  disch_then (qx_choose_then `pre_fn` strip_assume_tac) >>
  `pre_fn.fn_name = efn.fn_name` by
    metis_tac[lookup_function_selected_name] >>
  `!f. MEM f (prune_unit_fcg_unreachable pre_unit
       (fcg_analyze pre_unit.cu_context)).cu_context.ctx_functions ==>
       EVERY (\i. i.inst_opcode <> RETURNDATACOPY) (fn_insts f)` by
    (rpt strip_tac >>
     `f = pre_fn` by
       (irule prune_unit_fcg_leaf_entry >>
        conj_tac >- fs[EVERY_MEM] >>
        qexists `pre_unit` >> simp[]) >>
     gvs[EVERY_MEM]) >>
  drule_at (Pat `run_callee_first _ _ _ _ _ = _`)
    (Q.INST [`P` |-> `\op. op <> RETURNDATACOPY`]
      run_callee_first_opcode_every) >>
  disch_then assume_tac >> rpt gen_tac >> disch_then strip_assume_tac >>
  qpat_x_assum `!f'. _` (qspec_then `fn` mp_tac) >>
  simp[EVERY_MEM] >>
  impl_tac
  >- (conj_tac
      >- metis_tac[execute_o1_fn_pass_no_returndatacopy] >>
      fs[EVERY_MEM]) >>
  simp[]
QED
