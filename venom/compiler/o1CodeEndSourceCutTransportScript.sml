(* Cut-local read-site transport.  Whole-run code/data facts stay unguarded. *)
Theory o1CodeEndSourceCutTransport
Ancestors
  o1CodeEndCfgBoundary
  o1LabelReadinessSsa o1LabelReadinessSimplify o1LabelReadinessCfgNorm
  o1ContractSimplifyCfg o1ContractMakeSsa o1ContractMakeSsaSrc
  makeSsaCurrentLockstep o1FrameLockstep lowerDloadPublicTrace memSafeRun
  o1SafeUpto unitMemInv ctxLookupAgreeHelpers
  o1ContractSimplifyCfgSrcFrame o1PassLift simplifyCfgControl
  simplifyCfgCorrectness simplifyCfgStaticInterface simplifyCfgProof
  simplifyCfgDefs venomInst venomWf list rich_list o1PassContract
  makeSsaDefs makeSsaCurrentSim makeSsaCurrentFrameRf venomState stateFrame unitShapeDefs
  o1ComposeSupport o1DretDesugarContract o1PipelineCompose fcgPruning

Theorem code_end_simplify_cfg_section_upto[local]:
  ctx_pass_stage rp (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s) C vs ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s) C' vs
Proof
  strip_tac >>
  drule_all simplify_cfg_stage_frame_interface >>
  disch_then (qspec_then `vs.vs_labels` strip_assume_tac) >>
  fs[mem_inv_raw_reachable] >> conj_tac
  >- (drule list_rel_lookup_function >> simp[] >>
      disch_then (qspec_then `name` mp_tac) >>
      simp[optionTheory.OPTREL_def] >> metis_tac[]) >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
  >- (drule_all scfg_raw_dload_payload >> strip_tac >>
      rename1 `scfg_payload src s` >>
      `gas_cut n vs src` by
        (irule gas_cut_execution_frame >> metis_tac[scfg_payload_frame]) >>
      metis_tac[scfg_payload_dload_in_section]) >>
  fs[inst_dload_in_section_def]
QED

Theorem code_end_make_ssa_section_upto[local]:
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s) C vs ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s) C' vs
Proof
  strip_tac >>
  `C'.ctx_entry = C.ctx_entry` by metis_tac[make_ssa_stage_functions] >>
  fs[mem_inv_raw_reachable] >> conj_tac
  >- (drule_all make_ssa_src_stage_lookup >> strip_tac >> metis_tac[]) >>
  rpt strip_tac >> rename1 `raw_reachable vs C' fn' inst' s'` >>
  reverse (Cases_on `inst'.inst_opcode = DLOAD \/ inst'.inst_opcode = DLOADBYTES`)
  >- fs[inst_dload_in_section_def] >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  drule_all make_ssa_src_stage_observation >> strip_tac >>
  `gas_cut n vs s` by
    (irule gas_cut_execution_frame >> metis_tac[]) >>
  `s'.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `execution_frame s' = execution_frame s` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  `inst_dload_in_section inst s` by metis_tac[] >>
  qpat_x_assum `inst_dload_in_section inst s`
    (assume_tac o REWRITE_RULE [inst_dload_in_section_def]) >>
  rewrite_tac[inst_dload_in_section_def] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS2] >> first_x_assum irule >> metis_tac[]
QED

(* The existing source transport keeps these static boundaries local. *)
Theorem code_end_simplify_cfg_no_label[local]:
  ctx_pass_stage rp (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\
  (!f i. MEM f C.ctx_functions /\ MEM i (fn_insts f) ==>
           ~MEM (Label "code_end") i.inst_operands) ==>
  (!f i. MEM f C'.ctx_functions /\ MEM i (fn_insts f) ==>
           ~MEM (Label "code_end") i.inst_operands)
Proof
  strip_tac >> drule simplify_cfg_stage_functions >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM source C.ctx_functions` >>
  `o1_fn_shape C source` by metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels source)` by fs[o1_fn_shape_def, wf_function_def] >>
  `EVERY (\bb. bb.bb_label <> "code_end" /\
    EVERY (\i. ~MEM (Label "code_end") i.inst_operands) bb.bb_instructions)
      source.fn_blocks` by
    (fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
        unitShapeDefsTheory.reserved_label_def, EVERY_MEM,
        fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  fs[GSYM cfg_label_absent_def] >>
  drule_all cfg_absent_iter >>
  disch_then (qspec_then `LENGTH source.fn_blocks` assume_tac) >>
  fs[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def, cfg_label_absent_def, EVERY_MEM,
     fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem code_end_make_ssa_no_label[local]:
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  (!f i. MEM f C.ctx_functions /\ MEM i (fn_insts f) ==>
           ~MEM (Label "code_end") i.inst_operands) ==>
  (!f i. MEM f C'.ctx_functions /\ MEM i (fn_insts f) ==>
           ~MEM (Label "code_end") i.inst_operands)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?n. n < LENGTH C'.ctx_functions /\ f = EL n C'.ctx_functions` by
    metis_tac[MEM_EL] >>
  `n < LENGTH C.ctx_functions` by metis_tac[make_ssa_stage_length] >>
  drule_all make_ssa_stage_el >> strip_tac >>
  `o1_fn_shape C (EL n C.ctx_functions)` by
    metis_tac[o1_ctx_shape_def, EVERY_MEM, EL_MEM] >>
  `~MEM "code_end" (fn_labels (EL n C.ctx_functions))` by
    (fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
       unitShapeDefsTheory.reserved_label_def, fn_labels_def, EVERY_MEM, MEM_MAP] >>
     metis_tac[]) >>
  `EVERY (\i. ~MEM (Label "code_end") i.inst_operands)
     (fn_insts (EL n C.ctx_functions))` by
    (simp[EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `wf_function (EL n C.ctx_functions)` by fs[o1_fn_shape_def] >>
  fs[EVERY_MEM] >>
  metis_tac[o1LabelReadinessSsaTheory.make_ssa_current_fn_label_absent]
QED

Theorem code_end_pre_walk_section_upto[local]:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit supply =
    SOME (pre,supply') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok supply /\
  EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f))
    unit.cu_context.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s)
    unit.cu_context vs /\
  (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
     ~MEM (Label "code_end") i.inst_operands) ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s)
    pre.cu_context vs /\
  (!f i. MEM f pre.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
     ~MEM (Label "code_end") i.inst_operands)
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  `unit_labels_wf mid /\ ir_supply_inst_ok t /\ o1_ctx_shape mid.cu_context /\
   ctx_pass_stage rp (CFP_Simple VP_SimplifyCFG) any_view
      unit.cu_context mid.cu_context` by
    (mp_tac (Q.INST [`pass` |-> `CFP_Simple VP_SimplifyCFG`,
       `u` |-> `unit`, `u'` |-> `mid`, `s` |-> `supply`, `s'` |-> `t`]
       mapped_pass_stage) >> simp[o1_contract_simplify_cfg_pre_walk]) >>
  `ctx_pass_stage rp (CFP_Simple VP_DretDesugar) any_view
      mid.cu_context pre.cu_context` by
    (drule unit_labels_wf_namespace >> strip_tac >>
     mp_tac (Q.INST [`pass` |-> `CFP_Simple VP_DretDesugar`,
       `u` |-> `mid`, `u'` |-> `pre`, `s` |-> `t`, `s'` |-> `supply'`]
       mapped_pass_stage) >> simp[o1_contract_dret_desugar_pre_walk]) >>
  `pre.cu_context = mid.cu_context` by metis_tac[dret_desugar_stage_identity] >>
  conj_tac
  >- metis_tac[code_end_simplify_cfg_section_upto] >>
  metis_tac[code_end_simplify_cfg_no_label]
QED

Theorem code_end_source_prefix_transport_upto:
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit supply =
    SOME (pre,supply') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok supply /\
  EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f))
    unit.cu_context.ctx_functions /\
  fcg = fcg_analyze pre.cu_context /\ pre.cu_context.ctx_entry = SOME entry /\
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view
    (prune_unit_fcg_unreachable pre fcg).cu_context C1 /\
  EVERY make_ssa_input_ok
    (prune_unit_fcg_unreachable pre fcg).cu_context.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (\ctx fn inst s. (gas_cut n vs s ==> inst_dload_in_section inst s) /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    unit.cu_context vs /\
  (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
     ~MEM (Label "code_end") i.inst_operands) ==>
  mem_inv (\ctx fn inst s. (gas_cut n vs s ==> inst_dload_in_section inst s) /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section) C1 vs /\
  (!f i. MEM f C1.ctx_functions /\ MEM i (fn_insts f) ==>
     ~MEM (Label "code_end") i.inst_operands)
Proof
  strip_tac >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s)
    unit.cu_context vs` by
    (irule mem_inv_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all code_end_pre_walk_section_upto >> strip_tac >>
  `o1_ctx_shape pre.cu_context` by metis_tac[o1_pre_walk_sim] >>
  `o1_ctx_shape (prune_unit_fcg_unreachable pre fcg).cu_context` by
    metis_tac[o1_ctx_shape_prune] >>
  `mem_inv (\ctx fn inst s. (gas_cut n vs s ==> inst_dload_in_section inst s) /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    pre.cu_context vs` by
    (fs[mem_inv_raw_reachable] >> metis_tac[raw_reachable_code_data]) >>
  `mem_inv (\ctx fn inst s. (gas_cut n vs s ==> inst_dload_in_section inst s) /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    (prune_unit_fcg_unreachable pre fcg).cu_context vs` by
    (mp_tac (Q.INST [`unit` |-> `pre`, `M` |-> `\ctx fn inst s.
       (gas_cut n vs s ==> inst_dload_in_section inst s) /\
       s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section`]
       o1_prune_sim) >> simp[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s)
    (prune_unit_fcg_unreachable pre fcg).cu_context vs` by
    (irule mem_inv_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> inst_dload_in_section inst s)
    C1 vs` by metis_tac[code_end_make_ssa_section_upto] >>
  conj_tac
  >- (fs[mem_inv_raw_reachable] >> metis_tac[raw_reachable_code_data]) >>
  `!f i. MEM f (prune_unit_fcg_unreachable pre fcg).cu_context.ctx_functions /\
         MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands` by
    (mp_tac (Q.INST [`unit` |-> `pre`, `P` |-> `\f. !i.
       MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands`]
       o1_prune_every) >> simp[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[code_end_make_ssa_no_label]
QED
