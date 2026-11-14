Theory fnStaticAbortInstSteps
Ancestors
  fnStaticAbortBodyFacts fnBlockBodyClasses fnStaticAbortBoundary
  fnFrameDeepHalt fnFrameDeepAbort fnBlockBodySteps codegenRel

Theorem body_abort_ordinary_ok:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n ast1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb)) ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n ast = AsmOK ast1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 ast1 /\
      ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)
Proof
  strip_tac >> drule_all body_inv_abort_memory >> strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_ordinary_ok >> simp[]
QED

Theorem body_abort_gas_ok:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
    inst.inst_opcode = GAS /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n ast1.
      generate_inst_plan liveness dfg cfg fn inst
        (live_vars_at liveness bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb)) ps' = SOME (rest', ps_after) /\
      rest_ops = ops ++ rest' /\
      asm_steps lo o2pc prog n ast = AsmOK ast1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 ast1 /\
      ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)
Proof
  strip_tac >> drule_all body_inv_abort_memory >> strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_gas_ok >> simp[]
QED

(* Shared preparation consumes canonical planning interfaces, not their
   implementation proofs. Keep their exact facts unnormalized for matching. *)
val abort_terminal_facts_tac =
  drule_all body_inv_abort_memory >> strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule body_plan_inv_equiv >> disch_then drule >> disch_then drule >>
  strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_plan_inv_label_resolve >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_plan_inv`
    (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]);

Theorem body_abort_halt_step:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Halt vs1 ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast (Halt vs1)
Proof
  strip_tac >> abort_terminal_facts_tac >>
  drule_all gen_inst_halt_frame_sim_deep >>
  disch_then(qx_choosel_then [`n`,`out`] strip_assume_tac) >>
  simp[body_result_abort_def] >>
  qexistsl_tac [`n`,`out`] >> simp[] >>
  qpat_x_assum `lo = SND (compute_label_offsets prog)` (fn hlo =>
    qpat_x_assum `o2pc = build_offset_to_pc prog` (fn hpc =>
      qpat_x_assum `asm_steps lo o2pc prog n ast = AsmHalt out`
        (ACCEPT_TAC o REWRITE_RULE [hlo, hpc])))
QED

Theorem body_abort_abort_step:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    ~in_static_abort_prefix fn vs /\ ~in_revert_forward fn vs /\
    inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = Abort a vs1 ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast (Abort a vs1)
Proof
  strip_tac >> abort_terminal_facts_tac >>
  `inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc (execute_plan cpl.cp_initial_fmp revert_postamble)` by
    (strip_tac >> qexistsl_tac [`roff`, `rpc`] >> simp[]) >>
  drule_all gen_inst_abort_frame_sim_deep >>
  simp[body_result_abort_def, venom_asm_terminal_rel_def] >> metis_tac[]
QED

Theorem body_abort_ret_step:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    LENGTH (compute_operands inst) <= 16 /\
    step_inst fuel ctx inst vs = IntRet ret vs1 ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast (IntRet ret vs1)
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_ret_step >> simp[body_result_abort_def]
QED

Theorem body_abort_revert_step:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
    revert_forward_pair bb k j /\
    (!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops) ==>
    (!t. exec_block fuel ctx bb vs <> OK t) /\
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast
      (exec_block fuel ctx bb vs)
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_revert_step >>
  metis_tac[body_result_abort_from_strict]
QED
