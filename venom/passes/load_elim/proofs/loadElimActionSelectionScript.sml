Theory loadElimActionSelection
Ancestors
  loadElimOriginHelpers simplifyCfgPhiRepair cfgNormBase venomWf list rich_list finite_map venomWfProps

Theorem le_collected_action_at_position:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = inst /\
  phi_action_lookup (collect_phi_actions m ctx cfg result fn) inst.inst_id = SOME out ==>
  ?pa addr dst vs.
    MEM pa (collect_phi_actions m ctx cfg result fn) /\
    pa.pa_phi_out = out /\ pa.pa_load_lbl = bb.bb_label /\
    pa.pa_load_id = inst.inst_id /\
    inst.inst_opcode = ctx.lctx_config.lc_load /\
    inst.inst_operands = [addr] /\ inst.inst_outputs = [dst] /\
    FLOOKUP (unwrap_load_lattice (df_at NONE result bb.bb_label n))
      (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg []) inst) = SOME vs /\
    LENGTH vs > 1 /\
    compute_phi_action m cfg result
      (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg []) inst) bb.bb_label inst = SOME pa
Proof
  strip_tac >> drule phi_action_lookup_member >> strip_tac >>
  drule collect_phi_actions_member >> strip_tac >>
  rename1 `MEM origin fn.fn_blocks` >>
  drule compute_phi_action_origin >> strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\b. MAP (\i. i.inst_id) b.bb_instructions)
     fn.fn_blocks))` by fs[wf_function_def, fn_inst_ids_distinct_def] >>
  `origin = bb` by
    (drule distinct_projection_member_eq >>
     disch_then (qspecl_then [`origin`, `bb`, `inst.inst_id`] mp_tac) >>
     simp[MEM_MAP] >> metis_tac[EL_MEM]) >> gvs[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule wf_function_block_inst_ids_distinct >> metis_tac[]) >>
  `idx = n` by
    (drule ALL_DISTINCT_EL_IMP >>
     disch_then (qspecl_then [`idx`, `n`] mp_tac) >> simp[EL_MAP]) >>
  gvs[] >> metis_tac[]
QED
