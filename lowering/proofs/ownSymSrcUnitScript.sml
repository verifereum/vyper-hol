(* Source-side facts for symbolic codegen that support observing self.code. *)
Theory ownSymSrcUnit
Ancestors
  runtimeLabelReadiness deployLabelReadiness runtimeLabelInvariant
  runtimeSymSrcData deploySymSrcData deployEntryLayout
  loweringShapeProps supportedProgram ctorDeployShape
  sourceLabelFlow unitShapeDefs
  ctorDeployDefs compileVyper stackPlanTypes venomInst list

Theorem lower_vyper_runtime_unit_sym_src_ok_own:
  !tops rpolicy unit.
  o1_source_unit_ok unit /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  label_flow_own_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) unit.cu_data_segment /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)
Proof
  rpt gen_tac >> strip_tac >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       source_inst_ok ({"code_end"},T) inst` by
    metis_tac[lower_vyper_runtime_unit_label_checks] >>
  drule_all source_own_flow >> strip_tac >>
  rpt conj_tac >|
  [first_assum ACCEPT_TAC,
   metis_tac[],
   metis_tac[lower_vyper_runtime_unit_data_bytes],
   metis_tac[lower_vyper_runtime_unit_no_runtime_begin]]
QED

Theorem lower_vyper_deploy_unit_sym_src_ok_own:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx ==>
  label_flow_own_ok dunit.cu_context /\
  (!fn inst. MEM fn dunit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) dunit.cu_data_segment /\
  ((?fn inst. MEM fn dunit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") dunit.cu_data_segment)
Proof
  rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule_all checked_lower_vyper_deploy_unit_source_shape >> strip_tac >>
  `!fn inst. MEM fn dunit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       source_inst_ok ({"code_end"},T) inst` by
    (rpt strip_tac >> irule lower_vyper_deploy_unit_label_checks >>
     simp[] >> metis_tac[]) >>
  drule_all source_own_flow >> strip_tac >>
  rpt conj_tac >|
  [first_assum ACCEPT_TAC,
   metis_tac[],
   drule lower_vyper_deploy_unit_data_bytes >> simp[],
   drule lower_vyper_deploy_unit_runtime_section >>
   simp[EXISTS_MEM] >> rpt strip_tac >>
   qexists_tac `<| ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc] |>` >>
   simp[]]
QED
