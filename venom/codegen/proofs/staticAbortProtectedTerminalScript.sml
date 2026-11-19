(* Protected terminal boundaries: never enter either relaxed-memory cut. *)
Theory staticAbortProtectedTerminal
Ancestors
  fnStaticAbortBodyFacts symBlockBody symFrameControl codegenSymRel
  fnBlockBodySteps fnStaticAbortBoundary unitShapeDefs

Theorem sym_abort_protected_halt_step:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Halt vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs1)
Proof
  strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all body_inv_abort_memory >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all sym_halt_frame_sim_deep >>
  strip_tac >> irule sym_body_result_halt >> metis_tac[]
QED

Theorem sym_abort_protected_abort_step:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Abort a vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs1)
Proof
  strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all body_inv_abort_memory >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `(inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog)` by
    metis_tac[placed_revert_sym_code_label] >>
  `(inst.inst_opcode = ASSERT ==> ?off pc.
    FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc /\
    asm_block_at prog pc (execute_plan cpl.cp_initial_fmp revert_postamble))` by
    metis_tac[] >>
  drule_all sym_abort_frame_sim_deep >>
  strip_tac >> irule sym_body_result_abort >> metis_tac[]
QED

Theorem sym_abort_protected_ret_step:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = IntRet rv vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs1)
Proof
  strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >> strip_tac >>
  `inst.inst_opcode = RET` by metis_tac[codegen_ready_intret_opcode] >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (irule fnBlockBodyHelpersTheory.reachable_fn_mem_inst >>
     simp[] >> metis_tac[]) >>
  `ps'.ps_stack = []` by metis_tac[] >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all sym_ret_frame_sim_deep >>
  strip_tac >> irule sym_body_result_intret >> metis_tac[]
QED
