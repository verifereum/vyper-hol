Theory staticAbortProtectedGas
Ancestors
  fnStaticAbortBodyFacts symBlockBody symFrameControl fnBlockBodySteps
  unitShapeDefs venomInst symFrameControlDischargeOwn symFrameBoundaryPairing
  fnStaticAbortBoundary codegenSymRel

(* Only the current instruction needs memory separation.  Neither relaxed
   continuation is entered by this protected GAS step. *)
Theorem sym_body_abort_protected_gas_ok_reloc:
  body_inv_abort_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  asm_static_wf prog /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  strip_tac >>
  drule body_inv_abort_plan_reloc >> strip_tac >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_step_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  drule_all body_inv_abort_memory_reloc >> strip_tac >>
  `context_spill_step_safe cpl vs vs1` by metis_tac[] >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve_reloc >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_plan_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_reloc_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`ops`, `ps'`, `rest'`] >>
  qhdtm_assum `generate_inst_plan` (fn th => simp_tac bool_ss [th]) >>
  qpat_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ ps' = SOME (rest', ps_after)`
    (fn th => simp_tac bool_ss [th]) >>
  qpat_assum `rest_ops = ops ++ rest'` (fn th => simp_tac bool_ss [th]) >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] sym_gas_frame_sim_deep_own) >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- (qexists_tac `r` >> asm_simp_tac bool_ss []) >>
  fs[] >>
  qhdtm_assum `generate_inst_plan` (irule_at Any) >>
  qhdtm_assum `step_inst` (irule_at Any) >>
  qexists_tac `spill_base` >> gvs[is_terminator_def] >> metis_tac[]
QED

Theorem sym_body_abort_protected_gas_ok:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = OK vs1 /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest' n as1 ss1.
    generate_inst_plan liveness dfg cfg fn inst
      (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (SUC k - LENGTH (get_params bb.bb_instructions))
      (DROP (SUC k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps' = SOME (rest', ps_after) /\
    rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss1 /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1
Proof
  strip_tac >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_reloc_canonical]) >>
  `sym_frame_inv_own lo prog env as.as_code ctx cpl fn ret srest labs0 ps as ss` by
    metis_tac[sym_frame_inv_canonical_own] >>
  drule_at (Pat `body_inv_abort_reloc`)
    (SRULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`]
      sym_body_abort_protected_gas_ok_reloc)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`ops`, `ps'`, `rest'`, `n`, `as1`, `ss1`] >>
  simp[] >> metis_tac[sym_frame_inv_canonical_own]
QED
