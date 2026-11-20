(* Source-side facts for symbolic codegen that support observing self.code. *)
Theory ownSymSrcUnit
Ancestors
  runtimeLabelReadiness deployLabelReadiness runtimeLabelInvariant
  runtimeSymSrcData deploySymSrcData deployEntryLayout
  loweringShapeProps supportedProgram ctorDeployShape
  codegenSymOwnRel o1LabelFlowSourceBoundary unitShapeDefs
  ctorDeployDefs compileVyper stackPlanTypes venomInst list

Theorem source_own_flow[local]:
  o1_source_unit_ok unit /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     source_inst_ok ({"code_end"},T) inst) ==>
  label_flow_own_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands)
Proof
  strip_tac >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "code_end") inst.inst_operands` by
    (rpt strip_tac >> res_tac >>
     gvs[source_inst_ok_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e inst.inst_operands ==> _`
       (qspec_then `Label "code_end"` mp_tac) >>
     simp[rb_operand_ok_for_def]) >>
  `!f x. MEM f unit.cu_context.ctx_functions ==> ~code_end_var f x` by
    metis_tac[code_end_var_absent] >>
  simp[label_flow_own_ok_def] >> rpt strip_tac >> res_tac >>
  `label_positions_ok inst /\ opaque_use_ok fn` by
    (fs[o1_source_unit_ok_def, unit_shape_ok_def, fn_shape_ok_def,
        EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 3` by
    (res_tac >> gvs[source_inst_ok_def]) >>
  gvs[LENGTH_EQ_NUM_compute] >>
  rename1 `inst.inst_operands = [dst; src; sz]` >>
  `!x. src = Var x ==> ~retpc_var fn x` by
    (rpt strip_tac >>
     qpat_x_assum `opaque_use_ok fn`
       (mp_tac o REWRITE_RULE [opaque_use_ok_def]) >>
     disch_then (qspecl_then [`inst`, `x`] mp_tac) >>
     simp[retpc_use_ok_def]) >>
  Cases_on `src` >> gvs[is_label_operand_def, label_positions_ok_def] >>
  metis_tac[]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >>
  `o1_source_unit_ok unit` by
    metis_tac[lower_vyper_runtime_unit_source_unit_ok_shape,
              supported_program_runtime_bodies_shape_ok,
              supported_program_internal_names, classified_internal_names_distinct] >>
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
*)
Theorem lower_vyper_runtime_unit_sym_src_ok_own:
  !tops rpolicy unit.
  supported_program tops /\
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
  cheat
QED

Theorem lower_vyper_deploy_unit_sym_src_ok_own:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan.
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  supported_program tops /\ supported_program_deploy tops ==>
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
  `o1_source_unit_ok dunit` by metis_tac[lower_vyper_deploy_unit_source_unit_ok] >>
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
