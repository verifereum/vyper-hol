Theory o1LabelFlowSourcePreWalk
Ancestors
  o1LabelFlowSourceBoundary o1LabelFlowSourceCfgData o1LabelFlowSourceCfgLabels
  o1ComposeSupport o1ContractSimplifyCfg o1DretDesugarContract
  unitShapeDefs o1PassContract venomInst list o1ContractSimplifyCfgSrcStatic
  simplifyCfgDefs simplifyCfgPhiProps cfgTransform
  simplifyCfgStaticInterface simplifyCfgShapeCore simplifyCfgCorrectness

Theorem simplify_cfg_source_seed_free_flow:
  o1_fn_shape C f /\ fn_defs_reach_uses f /\
  EVERY (\i. raw_opcode_ok i.inst_opcode) (fn_insts f) /\
  label_flow_ok C /\ MEM f C.ctx_functions /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) ==>
  !i. MEM i (fn_insts (simplify_cfg_fn f)) ==>
    ~MEM (Label "code_end") i.inst_operands /\
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
     ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)` by
    (gvs[EVERY_MEM, raw_opcode_ok_def] >> metis_tac[]) >>
  `EVERY no_phis f.fn_blocks` by
    (gvs[no_phis_def, EVERY_MEM, fn_insts_def,
         MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `simplify_cfg_fn_ok f` by
    (irule simplify_cfg_fn_ok_no_phi >> gvs[o1_fn_shape_def]) >>
  `scfg_static f` by
    (simp[scfg_static_def] >>
     metis_tac[o1_fn_shape_def, fn_shape_ok_scfg_shape]) >>
  `!i. MEM i (fn_insts f) ==>
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])` by
    metis_tac[label_flow_seed_free_extract] >>
  gen_tac >> disch_tac >> conj_tac
  >- (irule simplify_cfg_fn_no_reserved_operand >>
      simp[reserved_label_def] >> metis_tac[]) >>
  conj_tac
  >- metis_tac[simplify_cfg_fn_no_codesize] >>
  metis_tac[simplify_cfg_fn_codecopy_runtime_begin]
QED

Theorem o1_pre_walk_seed_free_flow:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s /\
  o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  unit_fmp_unsealed unit /\ label_flow_ok unit.cu_context /\
  (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  !f i. MEM f unit'.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands /\
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
     ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`]
            mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t`, `u'` |-> `unit'`]
            mapped_pass_stage) >>
  impl_tac
  >- simp[o1_contract_dret_desugar_pre_walk, unit_labels_wf_namespace] >>
  strip_tac >>
  `unit'.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  `mid.cu_context.ctx_functions =
     MAP simplify_cfg_fn unit.cu_context.ctx_functions` by
    metis_tac[simplify_cfg_stage_functions] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP] >> irule simplify_cfg_source_seed_free_flow >>
  qexists_tac `unit.cu_context` >>
  gvs[o1_ctx_shape_def, o1_source_unit_ok_def, unit_defs_reach_uses_def,
      EVERY_MEM] >> metis_tac[]
QED
