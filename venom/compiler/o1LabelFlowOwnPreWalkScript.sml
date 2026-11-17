Theory o1LabelFlowOwnPreWalk
Ancestors
  codegenSymOwnRel
  o1LabelFlowCompose
  o1LabelFlowSourceCfgLabels
  o1LabelReadinessSsa
  o1LabelFlowStaticContracts
  o1ComposeSupport
  o1ContractSimplifyCfg
  o1DretDesugarContract
  o1PassContract
  o1LabelFlowSourceBoundary
  unitShapeDefs
  venomInst
  list

Theorem o1_pre_walk_seed_free_own_flow:
  !rpolicy unit s unit' s'.
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s /\
  o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  unit_fmp_unsealed unit /\ label_flow_own_ok unit.cu_context /\
  (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  label_flow_own_ok unit'.cu_context /\
  (!f i. MEM f unit'.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands)
Proof
  rpt gen_tac >> strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`]
            mapped_pass_stage) >>
  (impl_tac >- simp[o1_contract_simplify_cfg_pre_walk]) >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t`, `u'` |-> `unit'`]
            mapped_pass_stage) >>
  (impl_tac
   >- simp[o1_contract_dret_desugar_pre_walk, unit_labels_wf_namespace]) >>
  strip_tac >>
  `unit'.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  `mid.cu_context.ctx_functions =
     MAP simplify_cfg_fn unit.cu_context.ctx_functions` by
    metis_tac[simplify_cfg_stage_functions] >>
  `!f i. MEM f unit'.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
     ~MEM (Label "code_end") i.inst_operands` by
    (simp[] >> rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >>
     rename1 `MEM src unit.cu_context.ctx_functions` >>
     irule simplify_cfg_fn_no_reserved_operand >>
     simp[reserved_label_def] >> qexistsl [`unit.cu_context`, `src`] >>
     gvs[o1_ctx_shape_def, o1_source_unit_ok_def, unit_defs_reach_uses_def,
         EVERY_MEM, raw_opcode_ok_def, reserved_label_def] >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  irule label_flow_own_ok_from_code_end_use >> conj_tac
  >- metis_tac[code_end_var_absent] >>
  gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]
QED
