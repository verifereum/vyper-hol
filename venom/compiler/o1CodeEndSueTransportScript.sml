Theory o1CodeEndSueTransport
Ancestors
  o1ContractSue o1LabelFlowSueNegative o1LabelFlowLateSue singleUseExpansionSupplySim
  singleUseExpansionSupplyProofs singleUseExpansionDefs o1PassContract
  codegenSymRel irSupply venomInst venomFnScheduleRunner venomFnInstsProofs list
  o1PassLift o1ContractCfgNorm lowerDloadSourceInterface

Theorem sue_project_fresh_assign[local]:
  a.inst_outputs = [v] /\ ~MEM v (fn_ir_vars f) /\
  ((a.inst_opcode = ASSIGN /\ ?w. a.inst_outputs = [w] /\
      MAP (\op. case op of Var x => project x | other => other)
        a.inst_operands = [project w]) \/
   (?i. MEM i (fn_insts f) /\ a.inst_opcode = i.inst_opcode /\
     a.inst_outputs = i.inst_outputs /\
     (!w. MEM w i.inst_outputs ==> project w = Var w) /\
     MAP (\op. case op of Var x => project x | other => other)
       a.inst_operands = i.inst_operands)) ==>
  MAP (\op. case op of Var x => project x | other => other)
    a.inst_operands = [project v]
Proof
  strip_tac >> gvs[] >> metis_tac[ld_original_output_support, MEM]
QED

Theorem sue_project_segment[local]:
  sue_expand_inst_supply dfg si i = (segment,sj) /\
  (!v. MEM (Var v) i.inst_operands ==> project v = Var v) /\
  (!a v. MEM a (BUTLAST segment) /\ a.inst_outputs = [v] ==>
    MAP (\op. case op of Var x => project x | other => other)
      a.inst_operands = [project v]) ==>
  MAP (\op. case op of Var x => project x | other => other)
    (LAST segment).inst_operands = i.inst_operands
Proof
  strip_tac >> drule sue_expand_inst_supply_precise_provenance >> strip_tac >>
  `LENGTH i.inst_operands = LENGTH (LAST segment).inst_operands` by
    metis_tac[LIST_REL_LENGTH] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rpt strip_tac >>
  rename1 `x < LENGTH (LAST segment).inst_operands` >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  `MEM (EL x i.inst_operands) i.inst_operands` by metis_tac[MEM_EL] >>
  Cases_on `EL x i.inst_operands` >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum (drule_at (Pat `MEM _ (FRONT _)`)) >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Theorem sue_segment_project_ready[local]:
  ir_supply_inst_ok si /\ set (fn_ir_vars f) SUBSET set si.irs_used_vars /\
  sue_expand_inst_supply dfg si i = (segment,sj) /\
  (!v. MEM (Var v) i.inst_operands ==> MEM v (fn_ir_vars f)) /\
  (!v. MEM v (fn_ir_vars f) ==> project v = Var v) /\
  (!a. MEM a segment ==> MEM a (fn_insts g)) /\
  (!a. MEM a (fn_insts g) ==>
    (a.inst_opcode = ASSIGN /\ ?w. a.inst_outputs = [w] /\
      MAP (\op. case op of Var x => project x | other => other)
        a.inst_operands = [project w]) \/
    (?k. MEM k (fn_insts f) /\ a.inst_opcode = k.inst_opcode /\
      a.inst_outputs = k.inst_outputs /\
      (!w. MEM w k.inst_outputs ==> project w = Var w) /\
      MAP (\op. case op of Var x => project x | other => other)
        a.inst_operands = k.inst_operands)) ==>
  MAP (\op. case op of Var x => project x | other => other)
    (LAST segment).inst_operands = i.inst_operands
Proof
  strip_tac >> irule sue_project_segment >>
  reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
  irule sue_project_fresh_assign >> conj_tac >- simp[] >>
  qexists_tac `f` >> conj_tac
  >- (drule_all sue_expand_inst_supply_segment >> strip_tac >>
      gvs[rich_listTheory.FRONT_APPEND_NOT_NIL, EVERY_MEM,
          MEM_FLAT, MEM_MAP, pred_setTheory.SUBSET_DEF] >> metis_tac[MEM]) >>
  first_x_assum irule >> first_x_assum irule >>
  Cases_on `segment` >> gvs[] >> metis_tac[rich_listTheory.MEM_FRONT, MEM]
QED

Theorem sue_frame_codecopy_projection[local]:
  ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  sue_frame_align C C' fn fn' s0 inst' t /\ inst'.inst_opcode = CODECOPY ==>
  ?inst u project.
    frame_reach C fn s0 inst u /\ inst.inst_opcode = CODECOPY /\
    MAP (\op. case op of Var x => project x | other => other)
      inst'.inst_operands = inst.inst_operands /\
    LIST_REL (\op newop. eval_operand newop t = eval_operand op u)
      inst.inst_operands inst'.inst_operands /\
    execution_frame u = execution_frame t /\
    (!v. code_end_var fn' v ==> ?x. project v = Var x /\ code_end_var fn x)
Proof
  strip_tac >> drule_all sue_expand_function_supply_projection_identity >>
  disch_then (qx_choose_then `project` strip_assume_tac) >>
  qpat_x_assum `sue_frame_align _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[sue_frame_align_def] >>
  disch_then (qx_choosel_then [`bb`,`bb_prime`,`bs`,`be`,`segs`,`i`,`j`,`u`,`b`] strip_assume_tac) >> gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `MEM (bb with bb_instructions := FLAT segs) fn'.fn_blocks` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  `!v. MEM (Var v) (EL u.vs_inst_idx bb.bb_instructions).inst_operands ==>
    MEM v (fn_ir_vars fn)` by
    metis_tac[sue_original_operand_covered, MEM_EL] >>
  drule_all sue_segments_supply_index_ready >>
  disch_then (qx_choosel_then [`si`,`sj`] strip_assume_tac) >>
  `EL j (EL u.vs_inst_idx segs) = LAST (EL u.vs_inst_idx segs) /\
   (EL j (EL u.vs_inst_idx segs)).inst_opcode = (EL u.vs_inst_idx bb.bb_instructions).inst_opcode /\
   LIST_REL (\op newop. eval_operand newop t = eval_operand op u)
     (EL u.vs_inst_idx bb.bb_instructions).inst_operands (EL j (EL u.vs_inst_idx segs)).inst_operands /\
   sue_state_rel (set (fn_ir_vars fn)) u t` by
    (drule_all sue_segment_operand_eval >> strip_tac >> gvs[]) >>
  `MAP (\op. case op of Var x => project x | other => other)
    (LAST (EL u.vs_inst_idx segs)).inst_operands = (EL u.vs_inst_idx bb.bb_instructions).inst_operands` by
    (irule sue_segment_project_ready >>
     qexistsl [`dfg_build_function fn`, `fn`, `fn'`, `si`, `sj`] >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
         qexists_tac `bb with bb_instructions := FLAT segs` >> simp[MEM_FLAT] >>
         qexists_tac `EL u.vs_inst_idx segs` >> simp[] >>
         drule sue_segments_supply_length >> metis_tac[MEM_EL]) >>
     gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  qexistsl [`EL u.vs_inst_idx bb.bb_instructions`, `u`, `project`] >>
  gvs[sue_state_rel_def] >> rpt strip_tac >>
  drule sue_projection_code_end_var >> disch_then irule >>
  qpat_x_assum `!j. MEM j (fn_insts fn') ==> _` mp_tac >> simp[]
QED

Theorem sue_code_end_stage_pairs[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_SingleUseExpansion) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY (o1_fn_row 6) C.ctx_functions ==>
  LIST_REL (\f g. g.fn_name = f.fn_name /\ fn_entry_label g = fn_entry_label f /\
    frame_sim L C C' f g /\
    wf_ssa f /\ fn_inst_wf f /\ wf_function f /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts f) /\
    ?si sj. ir_supply_inst_ok si /\ ir_supply_covers_fn si f /\
      sue_expand_function_supply si f = (g,sj)) C.ctx_functions C'.ctx_functions
Proof
  strip_tac >> `ctx_bisim C C'` by metis_tac[sue_stage_bisim] >>
  drule sue_stage_functions >> strip_tac >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  rename1 `n < LENGTH C'.ctx_functions` >> first_x_assum drule >> strip_tac >>
  drule sue_expand_function_supply_identity >> strip_tac >> simp[] >>
  `wf_ssa (EL n C.ctx_functions) /\ fn_inst_wf (EL n C.ctx_functions) /\
   wf_function (EL n C.ctx_functions) /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts (EL n C.ctx_functions))` by
    (gvs[o1_ctx_shape_def, o1_fn_shape_def, o1_fn_row_def, EVERY_EL] >> metis_tac[]) >>
  simp[] >- (irule sue_expand_function_supply_frame_sim >> metis_tac[]) >>
  metis_tac[]
QED

Theorem sue_code_end_stage_preserves[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_SingleUseExpansion) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY (o1_fn_row 6) C.ctx_functions /\ o1_run_state_ok vs /\
  code_end_offset_ok (raw_reachable vs) C ==>
  code_end_offset_ok (raw_reachable vs) C'
Proof
  strip_tac >>
  `ctx_bisim C C'` by metis_tac[sue_stage_bisim] >>
  drule_all sue_code_end_stage_pairs >>
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
  disch_then (qspec_then `source_name` mp_tac) >> simp[optionTheory.OPTREL_def] >>
  strip_tac >>
  `sue_frame_align C C' source_fn fn source_entry inst vs'` by
    (irule sue_frame_reach_align >> metis_tac[]) >>
  drule_all sue_frame_codecopy_projection >>
  disch_then (qx_choosel_then [`source_inst`, `source_state`, `project`] strip_assume_tac) >>
  `?y. project x = Var y /\ code_end_var source_fn y` by metis_tac[] >>
  `?d z. source_inst.inst_operands = [d; Var y; z]` by
    (qpat_x_assum `MAP _ _ = _` mp_tac >> simp[] >> metis_tac[]) >>
  `eval_operand (Var y) source_state = SOME w` by
    (gvs[LIST_REL_EL_EQN] >> first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  `raw_reachable vs C source_fn source_inst source_state` by metis_tac[frame_reach_raw_reachable] >>
  `source_state.vs_labels = vs'.vs_labels` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >> simp[]) >>
  qpat_x_assum `code_end_offset_ok _ _` mp_tac >>
  simp[code_end_offset_ok_def] >> metis_tac[]
QED

Theorem sue_code_end_run_contract:
  o1_stage_contract rpolicy D (EL 6 o1_fn_passes)
    (o1_walk_view rpolicy 6) (o1_pre 6)
    (\C s. o1_inv D 6 C s /\ code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 7 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  mp_tac sue_stage_walk >>
  simp[o1_run_contract_def, o1_stage_contract_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ctx_sim_fuel (pass_fuel (EL 6 o1_fn_passes) C') D C C' s s /\
   o1_inv D 7 C' s` by (first_x_assum irule >> simp[]) >>
  simp[] >>
  `EL 6 o1_fn_passes = CFP_Simple VP_SingleUseExpansion` by EVAL_TAC >>
  fs[o1_inv_def, o1_ssa_inv_def] >> irule sue_code_end_stage_preserves >>
  simp[] >> qexistsl [`C`, `rpolicy`, `o1_walk_view rpolicy 6`] >>
  fs[o1_pre_def, o1_fn_row_def, o1_lowered_inv_def]
QED
