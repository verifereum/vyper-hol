Theory o1CodeEndCfgNormTransport
Ancestors
  o1ContractCfgNorm o1ContractCfgNormStep cfgNormSupplySim cfgNormDefs
  cfgNormSupplyProofs codegenSymRel o1LabelFlowLateCfgNorm irSupply
  lowerDloadPtrStatic o1PassContract o1PassLift list venomInst venomFnScheduleRunner
  contextCodegenRel venomExecProofs venomState venomFnInstsProofs

Theorem cfg_old_code_end_var[local]:
  !g x. code_end_var g x ==> !f.
  (!j v. MEM j (fn_insts g) /\ MEM v j.inst_outputs /\
    MEM v (fn_ir_vars f) /\
    (j.inst_opcode = ADD \/ j.inst_opcode = ASSIGN) ==>
    MEM j (fn_insts f)) ==>
  MEM x (fn_ir_vars f) ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- metis_tac[code_end_var_rules] >>
  rename1 `inst.inst_operands = [Var y]` >>
  `MEM inst (fn_insts f)` by metis_tac[] >>
  `MEM y (fn_ir_vars f)` by metis_tac[fn_ir_vars_operand, MEM] >>
  metis_tac[code_end_var_rules]
QED

Theorem cfg_split_old_definition[local]:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s f pred target = (g,t) /\
  MEM j (fn_insts g) /\ MEM x j.inst_outputs /\
  MEM x (fn_ir_vars f) /\ (j.inst_opcode = ADD \/ j.inst_opcode = ASSIGN) ==>
  MEM j (fn_insts f)
Proof
  rpt strip_tac >>
  (drule_all insert_split_supply_inst_image >> strip_tac
   >- (drule_all supply_split_outputs_distinct >>
       gvs[cfg_block_decl_vars_def, MEM_FLAT, MEM_MAP, EVERY_MEM,
           ir_supply_covers_fn_def, list_subset_def] >> metis_tac[]) >>
   rename1 `supply_inst_image _ _ _ _ old j` >>
   drule supply_inst_image_metadata >> strip_tac >>
   `j = old` by (irule supply_inst_image_unchanged >>
     gvs[] >> simp[is_terminator_def] >> metis_tac[]) >> gvs[])
QED

Theorem cfg_split_codecopy_back[local]:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\
  EVERY label_positions_ok (fn_insts f) /\
  ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s f pred target = (g,t) /\ fn_entry_state f s0 /\
  frame_reach C g s0 j v /\ j.inst_opcode = CODECOPY /\
  MEM (Var x) j.inst_operands /\ code_end_var g x ==>
  ?u. frame_reach C f s0 j u /\ code_end_var f x /\
    eval_operand (Var x) u = eval_operand (Var x) v /\
    execution_frame u = execution_frame v
Proof
  strip_tac >>
  `supply_frame_phase C f g s pred target split repls s0 j v` by
    (irule supply_frame_reach_phase >> metis_tac[]) >>
  gvs[supply_frame_phase_def]
  >- (drule_all supply_frame_body_witness >>
      disch_then (qx_choosel_then [`bb`,`inst`,`a`] strip_assume_tac) >>
      `inst.inst_opcode = CODECOPY` by metis_tac[] >>
      `a.vs_inst_idx < LENGTH bb.bb_instructions` by
        (gvs[active_inst_def] >> metis_tac[same_label_same_block]) >>
      `supply_inst_image pred.bb_label target.bb_label split.bb_label repls inst j` by
        (gvs[] >> irule supply_block_image_index_image >> simp[]) >>
      `j = inst` by
        (irule supply_inst_image_unchanged >>
         gvs[] >> simp[is_terminator_def] >> metis_tac[]) >>
      qpat_x_assum `j = inst` SUBST_ALL_TAC >>
      `MEM inst (fn_insts f)` by
        (simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
         qexists_tac `bb` >> simp[] >> metis_tac[MEM_EL]) >>
      `MEM x (fn_ir_vars f)` by metis_tac[fn_ir_vars_operand] >>
      `code_end_var f x` by
        (drule cfg_old_code_end_var >> disch_then irule >> simp[] >>
         rpt strip_tac >> irule cfg_split_old_definition >> metis_tac[]) >>
      qexists_tac `a` >> gvs[supply_state_agree_def, eval_operand_def]) >>
  drule supply_frame_split_witness >> strip_tac >>
  drule supply_split_opcodes >> rewrite_tac[EVERY_EL] >>
  disch_then (qspec_then `v.vs_inst_idx` mp_tac) >> gvs[]
QED

Theorem cfg_round_codecopy_back[local]:
  supply_norm_inv s f /\ EVERY label_positions_ok (fn_insts f) /\
  cfg_norm_round_supply s f = (g,changed,t) /\ fn_entry_state f s0 /\
  frame_reach C g s0 j v /\ j.inst_opcode = CODECOPY /\
  MEM (Var x) j.inst_operands /\ code_end_var g x ==>
  ?u. frame_reach C f s0 j u /\ code_end_var f x /\
    eval_operand (Var x) u = eval_operand (Var x) v /\
    execution_frame u = execution_frame v
Proof
  strip_tac >> drule cfg_norm_round_supply_cases >> strip_tac
  >- (qexists_tac `v` >> gvs[]) >>
  rename1 `insert_split_supply s f pred target = (g,t)` >>
  Cases_on `build_split_block_supply s pred target` >>
  rename1 `build_split_block_supply s pred target = (split,split_tail)` >>
  PairCases_on `split_tail` >>
  rename1 `build_split_block_supply s pred target = (split,repls,rest)` >>
  `rest = t` by gvs[insert_split_supply_def] >> gvs[] >>
  fs[supply_norm_inv_def] >>
  drule_all cfg_split_codecopy_back >> simp[]
QED

Theorem cfg_iter_codecopy_back[local]:
  !n s f g t. supply_norm_inv s f /\ EVERY label_positions_ok (fn_insts f) /\
  cfg_norm_iter_supply n s f = (g,t) ==>
  !s0 C j v x. fn_entry_state f s0 /\
  frame_reach C g s0 j v /\ j.inst_opcode = CODECOPY /\
  MEM (Var x) j.inst_operands /\ code_end_var g x ==>
  ?u. frame_reach C f s0 j u /\ code_end_var f x /\
    eval_operand (Var x) u = eval_operand (Var x) v /\
    execution_frame u = execution_frame v
Proof
  mp_tac (Q.INST [`R` |-> `\f g.
    fn_entry_label g = fn_entry_label f /\
    !s0 C j v x. fn_entry_state f s0 /\
      frame_reach C g s0 j v /\ j.inst_opcode = CODECOPY /\
      MEM (Var x) j.inst_operands /\ code_end_var g x ==>
      ?u. frame_reach C f s0 j u /\ code_end_var f x /\
        eval_operand (Var x) u = eval_operand (Var x) v /\
        execution_frame u = execution_frame v`]
    supply_iter_relation) >> BETA_TAC >> impl_tac
  >- (rpt conj_tac
      >- metis_tac[]
      >- (rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
          rpt gen_tac >> strip_tac >>
          `fn_entry_state g s0` by gvs[fn_entry_state_def] >>
          metis_tac[]) >>
      rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[supply_round_semantics] >>
      rpt gen_tac >> strip_tac >>
      drule_all cfg_round_codecopy_back >> simp[]) >>
  metis_tac[]
QED

Theorem cfg_fn_codecopy_back[local]:
  ctx_bisim C C' /\ supply_norm_inv s f /\ EVERY label_positions_ok (fn_insts f) /\
  cfg_norm_function_supply s f = (g,t) /\ fn_entry_state f s0 /\
  frame_reach C' g s0 j v /\ j.inst_opcode = CODECOPY /\
  MEM (Var x) j.inst_operands /\ code_end_var g x ==>
  ?u. frame_reach C f s0 j u /\ code_end_var f x /\
    eval_operand (Var x) u = eval_operand (Var x) v /\
    execution_frame u = execution_frame v
Proof
  strip_tac >> `frame_reach C g s0 j v` by
    metis_tac[supply_frame_reach_ctx_back] >>
  fs[cfg_norm_function_supply_def] >>
  drule_all cfg_iter_codecopy_back >> simp[]
QED

Theorem cfg_code_end_stage_pairs[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions ==>
  LIST_REL (\f g. g.fn_name = f.fn_name /\ fn_entry_label g = fn_entry_label f /\
    frame_sim L C C' f g /\
    EVERY label_positions_ok (fn_insts f) /\
    ?si sj. supply_norm_inv si f /\ cfg_norm_function_supply si f = (g,sj))
    C.ctx_functions C'.ctx_functions
Proof
  strip_tac >> `ctx_bisim C C'` by metis_tac[cfg_norm_stage_bisim] >>
  drule cfg_norm_stage_functions >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule cfg_norm_function_supply_identity >> strip_tac >> simp[] >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by simp[EL_MEM] >>
  drule_all cfg_norm_stage_fn_ok >> strip_tac >> simp[]
  >- (irule cfg_norm_function_supply_frame_sim >> metis_tac[]) >>
  simp[supply_norm_inv_def] >> metis_tac[]
QED

Theorem cfg_code_end_stage_preserves[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\ o1_run_state_ok vs /\
  code_end_offset_ok (raw_reachable vs) C ==>
  code_end_offset_ok (raw_reachable vs) C'
Proof
  strip_tac >> `ctx_bisim C C'` by metis_tac[cfg_norm_stage_bisim] >>
  drule_all cfg_code_end_stage_pairs >>
  disch_then (qspec_then `vs.vs_labels` assume_tac) >>
  simp[code_end_offset_ok_def] >> rpt gen_tac >> strip_tac >>
  `frame_origin vs C C' fn inst vs'` by
    (irule frame_sim_raw_origins >> simp[] >>
     fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def,
        ctx_pass_stage_def] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >>
  disch_then (qx_choosel_then [`source_fn`, `source_entry`] strip_assume_tac) >>
  rename1 `lookup_function source_name C.ctx_functions = SOME source_fn` >>
  drule list_rel_lookup_function >> simp[] >>
  disch_then (qspec_then `source_name` mp_tac) >> simp[optionTheory.OPTREL_def] >> strip_tac >>
  `MEM (Var x) inst.inst_operands` by simp[] >>
  drule_all cfg_fn_codecopy_back >>
  disch_then (qx_choose_then `source_state` strip_assume_tac) >>
  `raw_reachable vs C source_fn inst source_state` by metis_tac[frame_reach_raw_reachable] >>
  `source_state.vs_labels = vs'.vs_labels` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >> simp[]) >>
  qpat_x_assum `code_end_offset_ok _ _` mp_tac >>
  simp[code_end_offset_ok_def] >> metis_tac[]
QED

Theorem cfg_norm_code_end_run_contract:
  o1_stage_contract rpolicy D (EL 8 o1_fn_passes)
    (o1_walk_view rpolicy 8) (o1_pre 8)
    (\C s. o1_inv D 8 C s /\ code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 9 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  mp_tac cfg_norm_stage_walk >>
  simp[o1_run_contract_def, o1_stage_contract_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ctx_sim_fuel (pass_fuel (EL 8 o1_fn_passes) C') D C C' s s /\
   o1_inv D 9 C' s` by (first_x_assum irule >> simp[]) >>
  simp[] >>
  `EL 8 o1_fn_passes = CFP_Simple VP_CFGNormalization` by EVAL_TAC >>
  fs[o1_inv_def, o1_ssa_inv_def] >> irule cfg_code_end_stage_preserves >>
  simp[] >> qexistsl [`C`, `rpolicy`, `o1_walk_view rpolicy 8`] >> simp[]
QED
