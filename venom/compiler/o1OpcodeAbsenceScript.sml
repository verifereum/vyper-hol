(* The O1 pipeline keeps opcode absences across the whole unit.  For a
 * leaf entry, pruning also discards every other function.
 * TOP-LEVEL: o1_pipeline_opcode_absence,
 * o1_pipeline_leaf_entry_opcode_absence, mem_inv_create_size_ok_no_create.
 *)
Theory o1OpcodeAbsence
Ancestors
  o1PipelineCorrect venomPassDispatcherProps fcgPruning fcgDefs venomInst
  o1DftOpcodePreservation o1CfgOpcodePreservation o1SimpleStructuralOpcodes
  o1OpcodePassPreservation
  o1OpcodeRunnerPreservation o1LeafPruning
  venomPipelineDriver venomPassSchedule venomPipelineRunner venomCompilerWf
  venomWf list ctxLookupAgreeHelpers
  venomRunBounded unitMemInv ctxLookupAgree stepWriteFootprintBase contextCodegenRel
  o1PassContract

(* Opcode absence gives the CREATE-size invariant for arbitrary entry states. *)
Theorem mem_inv_create_size_ok_no_create:
  !ctx vs.
    venom_wf ctx /\
    (!fn inst. MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
               inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2) ==>
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s) ctx vs
Proof
  rpt strip_tac >> simp[mem_inv_raw_reachable] >> conj_tac
  >- (fs[venom_wf_def, ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def] >>
      Cases_on `lookup_function entry_name ctx.ctx_functions`
      >- metis_tac[lookup_function_not_mem] >>
      rename1 `lookup_function _ _ = SOME efn` >>
      `wf_function efn` by metis_tac[venomInstTheory.lookup_function_MEM] >>
      Cases_on `efn.fn_blocks` >>
      fs[wf_function_def, fn_has_entry_def, fn_entry_label_def,
         entry_block_def]) >>
  rpt strip_tac >>
  `lookup_function fn.fn_name ctx.ctx_functions = SOME fn` by
    (qspecl_then [`K T`, `ctx`, `ctx`, `vs`] mp_tac raw_reachable_ctx_agree >>
     simp[ctx_agree_def, fn_calls_within_def] >> impl_tac
     >- simp[listTheory.EVERY_MEM, inst_calls_within_def] >>
     disch_then drule >> simp[]) >>
  `MEM inst (fn_insts fn)` by
    (drule raw_reachable_active >>
     simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[listTheory.MEM_EL]) >>
  `inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  simp[inst_create_size_ok_def]
QED

Theorem prune_unit_opcode_every[local]:
  !unit fcg P.
  (!f. MEM f unit.cu_context.ctx_functions ==> EVERY P (fn_insts f)) ==>
  !f. MEM f (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions ==>
      EVERY P (fn_insts f)
Proof
  rpt gen_tac >> metis_tac[MEM_prune_unit_fcg_unreachable_functions]
QED

Theorem o1_pipeline_opcode_absence:
  !rpolicy unit out op.
    (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\
    o1_pipeline rpolicy unit = SOME out /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\
               MEM inst (fn_insts fn) ==> inst.inst_opcode <> op)
    ==>
    !fn inst. MEM fn out.po_unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) ==> inst.inst_opcode <> op
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `op = _ \/ _` mp_tac >>
  gvs[o1PipelineCorrectTheory.o1_pipeline_def,
      run_venom_pipeline_def, o1_pipeline_spec_def, AllCaseEqs()] >>
  disch_tac >>
  qpat_x_assum `run_pipeline_stages _ [] _ _ = _` mp_tac >>
  simp[run_pipeline_stages_def] >> strip_tac >>
  qpat_x_assum `op = _ \/ _` mp_tac >> gvs[] >> disch_tac >>
  `!f. MEM f pre_unit.cu_context.ctx_functions ==>
       EVERY (\i. i.inst_opcode <> op) (fn_insts f)` by
    (drule_at (Pat `run_pipeline_stages _ _ _ _ = _`)
       (Q.INST [`P` |-> `\opc. opc <> op`, `selected` |-> `K T`]
         run_pipeline_stages_selected_opcodes) >>
     disch_then (qspec_then `op` assume_tac) >> rpt strip_tac >>
     qpat_x_assum `!f'. _` (qspec_then `f` mp_tac) >> simp[] >>
     impl_tac
     >- (conj_tac
         >- (simp[EVERY_MEM] >>
             metis_tac[execute_o1_pre_walk_opcode_absence]) >>
         fs[EVERY_MEM] >> metis_tac[]) >>
     simp[]) >>
  `!f. MEM f (prune_unit_fcg_unreachable pre_unit
               (fcg_analyze pre_unit.cu_context)).cu_context.ctx_functions ==>
       EVERY (\i. i.inst_opcode <> op) (fn_insts f)` by
    (qspecl_then [`pre_unit`, `fcg_analyze pre_unit.cu_context`,
                 `\i. i.inst_opcode <> op`] mp_tac prune_unit_opcode_every >>
     simp[]) >>
  drule_at (Pat `run_callee_first _ _ _ _ _ = _`)
    (Q.INST [`P` |-> `\opc. opc <> op`] run_callee_first_opcode_every) >>
  disch_then (qspec_then `op` assume_tac) >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!f'. _` (qspec_then `fn` mp_tac) >> simp[] >>
  impl_tac
  >- (simp[EVERY_MEM] >> metis_tac[execute_o1_fn_pass_opcode_absence]) >>
  strip_tac >> fs[EVERY_MEM]
QED

Theorem execute_pre_walk_leaf_opcodes[local]:
  (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\
  MEM (PS_MapFunctions pass) o1_pipeline_spec.ps_pre_walk_stages /\
  execute_configured_fn_pass rp pass u s f = SOME out /\
  EVERY (\i. i.inst_opcode <> op /\ i.inst_opcode <> INVOKE)
    (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> op /\ i.inst_opcode <> INVOKE)
    (fn_insts out.fpo_function)
Proof
  simp[o1_pipeline_spec_def, EVERY_MEM] >>
  metis_tac[execute_o1_pre_walk_opcode_absence]
QED

Theorem o1_pipeline_leaf_entry_opcode_absence:
  !rpolicy unit out efn op.
    (op = RETURNDATACOPY \/ op = CREATE \/ op = CREATE2) /\
    o1_pipeline rpolicy unit = SOME out /\
    unit.cu_context.ctx_entry = SOME efn.fn_name /\
    lookup_function efn.fn_name unit.cu_context.ctx_functions = SOME efn /\
    (!inst. MEM inst (fn_insts efn) ==>
            inst.inst_opcode <> op /\ inst.inst_opcode <> INVOKE)
    ==>
    !fn inst. MEM fn out.po_unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) ==>
              inst.inst_opcode <> op
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  (* keep the opcode disjunction whole: gvs would split it *)
  qpat_x_assum `op = _ \/ _` mp_tac >>
  gvs[o1PipelineCorrectTheory.o1_pipeline_def,
      run_venom_pipeline_def, o1_pipeline_spec_def,
      AllCaseEqs()] >>
  disch_tac >>
  qpat_x_assum `run_pipeline_stages _ [] _ _ = _` mp_tac >>
  simp[run_pipeline_stages_def] >> strip_tac >>
  qpat_x_assum `op = _ \/ _` mp_tac >> gvs[] >> disch_tac >>
  `ctx_wf unit.cu_context` by fs[unit_wf_def, venom_wf_def] >>
  `ctx_wf pre_unit.cu_context` by
    metis_tac[run_pipeline_stages_ctx_wf] >>
  `pre_unit.cu_context.ctx_entry = SOME efn.fn_name` by
    metis_tac[run_pipeline_stages_entry] >>
  drule_at (Pat `run_pipeline_stages _ _ _ _ = _`)
    (Q.INST [`P` |-> `\opc. opc <> op /\ opc <> INVOKE`]
      run_pipeline_stages_lookup_opcodes) >>
  disch_then (qspecl_then [`op`, `efn.fn_name`, `efn`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- metis_tac[SRULE [o1_pipeline_spec_def] execute_pre_walk_leaf_opcodes] >>
      simp[EVERY_MEM]) >>
  disch_then (qx_choose_then `pre_fn` strip_assume_tac) >>
  `pre_fn.fn_name = efn.fn_name` by
    metis_tac[lookup_function_selected_name] >>
  `!f. MEM f (prune_unit_fcg_unreachable pre_unit
       (fcg_analyze pre_unit.cu_context)).cu_context.ctx_functions ==>
       EVERY (\i. i.inst_opcode <> op) (fn_insts f)` by
    (rpt strip_tac >>
     `f = pre_fn` by
       (irule prune_unit_fcg_leaf_entry >>
        conj_tac >- fs[EVERY_MEM] >>
        qexists `pre_unit` >> simp[]) >>
     gvs[EVERY_MEM]) >>
  drule_at (Pat `run_callee_first _ _ _ _ _ = _`)
    (Q.INST [`P` |-> `\opc. opc <> op`]
      run_callee_first_opcode_every) >>
  disch_then (qspec_then `op` assume_tac) >> rpt gen_tac >> disch_then strip_assume_tac >>
  qpat_x_assum `!f'. _` (qspec_then `fn` mp_tac) >>
  simp[EVERY_MEM] >>
  impl_tac
  >- (conj_tac
      >- metis_tac[execute_o1_fn_pass_opcode_absence] >>
      fs[EVERY_MEM]) >>
  simp[]
QED
