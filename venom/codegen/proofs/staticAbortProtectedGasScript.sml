Theory staticAbortProtectedGas
Ancestors
  fnStaticAbortBodyFacts symBlockBody symFrameControl fnBlockBodySteps
  unitShapeDefs venomInst

(* Only the current instruction needs memory separation.  Neither relaxed
   continuation is entered by this protected GAS step. *)
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
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_inv_abort_memory >> strip_tac >>
  `context_spill_step_safe cpl vs vs1` by metis_tac[] >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_plan_inv`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  (* Keep the partially matched theorem in the continuation rather than
     re-assuming its universally quantified implication with disch_then. *)
  drule_at_then (Pat `fn_frame_inv`)
    (drule_at_then (Pat `generate_inst_plan`)
      (drule_at_then (Pat `generated_plan_state_wf_marked`)
        (drule_at_then (Pat `sym_frame_inv`)
          (drule_at (Pat `MEM r cpl.cp_regions`)))))
    sym_gas_frame_sim_deep >>
  simp[is_terminator_def] >>
  disch_then (qspecl_then [`fuel`, `vs1`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  metis_tac[]
QED
