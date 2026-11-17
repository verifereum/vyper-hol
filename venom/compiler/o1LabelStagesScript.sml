(* Runtime operand-label absence follows the compiler's actual stage relation. *)
Theory o1LabelStages
Ancestors
  o1LabelReadiness o1PipelineCompose o1ComposeSupport o1PassContract
  o1ContractSimplifyCfg o1DretDesugarContract simplifyCfgReferences
  unitShapeDefs venomState finite_map list arithmetic

Theorem o1_runtime_codecopy_labels_bound:
  o1_ctx_shape C /\
  (!fn inst. MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !fn inst l.
    MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
    l IN FDOM vs.vs_labels
Proof
  rpt strip_tac >>
  `o1_fn_shape C fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `inst_shape_ok inst` by
    (fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `label_positions_ok inst` by fs[inst_shape_ok_def] >>
  `l = "runtime_begin"` by metis_tac[label_positions_codecopy] >>
  metis_tac[]
QED

Theorem ctx_pass_stage_no_runtime_begin:
  ctx_pass_stage rpolicy pass view C C' /\ o1_ctx_shape C /\
  (!fn inst. MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !fn inst. MEM fn C'.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  rpt strip_tac >>
  qpat_x_assum `ctx_pass_stage _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ctx_pass_stage_def]) >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >> gvs[] >>
  rename1 `fn_pass_step rpolicy pass observed s old out` >>
  `o1_fn_shape observed.cu_context old` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `!i. MEM i (fn_insts old) ==>
    ~MEM (Label "runtime_begin") i.inst_operands` by metis_tac[] >>
  drule_all fn_pass_step_no_runtime_begin >> metis_tac[]
QED

Theorem o1_pre_walk_no_runtime_begin:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !fn inst. MEM fn unit'.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_SimplifyCFG`,
                  `u` |-> `unit`, `u'` |-> `mid`, `s'` |-> `t`]
            mapped_pass_stage) >>
  impl_tac >- simp[o1_contract_simplify_cfg_pre_walk] >> strip_tac >>
  `!fn inst. MEM fn mid.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[ctx_pass_stage_no_runtime_begin] >>
  mp_tac (Q.INST [`rp` |-> `rpolicy`, `pass` |-> `CFP_Simple VP_DretDesugar`,
                  `u` |-> `mid`, `s` |-> `t`, `u'` |-> `unit'`]
            mapped_pass_stage) >>
  impl_tac
  >- (simp[o1_contract_dret_desugar_pre_walk] >>
      metis_tac[unit_labels_wf_namespace]) >>
  strip_tac >> metis_tac[ctx_pass_stage_no_runtime_begin]
QED

Theorem o1_stage_chain_no_runtime_begin:
  (!k. k <= n ==> o1_ctx_shape (stage k)) /\
  (!k. k < n ==>
    ctx_pass_stage rpolicy (EL k passes) any_view (stage k) (stage (SUC k))) /\
  (!fn inst. MEM fn (stage 0).ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  !k fn inst. k <= n /\ MEM fn (stage k).ctx_functions /\
    MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `k <= n /\ k < n` by decide_tac >>
  `o1_ctx_shape (stage k)` by metis_tac[] >>
  `ctx_pass_stage rpolicy (EL k passes) any_view (stage k) (stage (SUC k))`
    by metis_tac[] >>
  `!f i. MEM f (stage k).ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "runtime_begin") i.inst_operands` by metis_tac[] >>
  drule_all ctx_pass_stage_no_runtime_begin >> metis_tac[]
QED

Theorem o1_schedule_stages_no_runtime_begin:
  rows_step_contracts_from R rp 0 passes /\
  EVERY (R 0) u.cu_context.ctx_functions /\
  run_named_fn_schedules execute_configured_fn_pass rp passes names u s =
    SOME (u',s') /\
  o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!name. MEM name names <=> MEM name (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s /\
  (!fn inst. MEM fn u.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands) ==>
  unit_labels_wf u' /\ ir_supply_inst_ok s' /\
  ?stage.
    stage 0 = u.cu_context /\ stage (LENGTH passes) = u'.cu_context /\
    (!k. k <= LENGTH passes ==>
      o1_ctx_shape (stage k) /\
      (stage k).ctx_entry = u.cu_context.ctx_entry /\
      (stage k).ctx_global_reserved = u.cu_context.ctx_global_reserved /\
      ctx_fn_names (stage k) = ctx_fn_names u.cu_context /\
      EVERY (R k) (stage k).ctx_functions) /\
    (!k. k < LENGTH passes ==>
      ctx_pass_stage rp (EL k passes) any_view (stage k) (stage (SUC k)) /\
      (callee_first names u.cu_context.ctx_functions ==>
       ctx_pass_stage rp (EL k passes) (walk_view R rp (SUC k) (DROP (SUC k) passes))
         (stage k) (stage (SUC k)))) /\
    (!k fn inst. k <= LENGTH passes /\
      MEM fn (stage k).ctx_functions /\ MEM inst (fn_insts fn) ==>
      ~MEM (Label "runtime_begin") inst.inst_operands)
Proof
  strip_tac >> drule_all o1_schedule_stages >> strip_tac >>
  simp[] >> qexists_tac `stage` >> simp[] >>
  mp_tac (Q.INST [`n` |-> `LENGTH passes`, `rpolicy` |-> `rp`]
    o1_stage_chain_no_runtime_begin) >>
  impl_tac >- metis_tac[] >> simp[]
QED
