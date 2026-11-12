(* Coverage across a block edge, starting from a restored related point. *)
Theory fmpStageCoverFrameBlock
Ancestors
  fmpStageCoverInv fmpStageCoverBack fmpStageBlockSim fmpStageOpSteps
  fmpStageOpBase fmpStageRel fmpStepLayout fmpLowerDefs
  ptrDiscipline contextCodegenRel o1PassContract passSimulationDefs
  fnBlockBodyHelpers lowerDloadPtrRawReachable stackPlanGen
  venomExecSemantics venomStepProps venomState venomInst
  finite_map words list

Theorem fmp_cov_block_point:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\
  active_inst fn' ti t /\ is_terminator ti.inst_opcode /\
  step_inst fuel C' ti t = OK t2 /\ ~t2.vs_halted /\
  enters_block fn' t2 t3 /\ active_inst fn' ti' t3 /\
  frame_reachable vs C stk PG G tn fn ti s /\ active_inst fn ti s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' ==>
  ?G1 tn1 inst s1.
    frame_reachable vs C stk PG G1 tn1 fn inst s1 /\
    active_inst fn inst s1 /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      stk PG G1 tn1 fn s1 lo t3 ts /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_cov_stack C' stk ts stk'
Proof
  strip_tac >>
  `MEM ti.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[step_ok_terminator_jump, MEM] >>
  `terminates (step_inst fuel C' ti t)` by simp[terminates_def] >>
  `~MEM ti.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI]` by
    (gvs[MEM] >> simp[]) >>
  `terminates (step_inst fuel C ti s)` by
    (irule fmp_stage_back_kept >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `?lbl inst'. step_inst fuel C ti s = OK (jump_to lbl s) /\
     active_inst fn' inst' t /\
     !k'. step_inst k' C' inst' t = OK (jump_to lbl t)` by
    (irule fmp_stage_jump_step >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[MEM]) >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  `inst' = ti` by
    metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  `t2 = jump_to lbl t` by metis_tac[exec_result_11] >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  `fn_labels fn' = fn_labels fn` by
    (fs[fmp_stage_lowered_def] >>
     irule fmp_lower_function_preserves_labels >>
     qexistsl_tac [`ctx`, `sp`, `sp'`] >> simp[fmp_lower_function_def]) >>
  `MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (fs[enters_block_def, jump_to_def] >>
     metis_tac[lookup_block_mem_fn_labels, fn_labels_def]) >>
  drule_all fmp_stage_back_block_entry >> strip_tac >>
  `?u. enters_block fn' (jump_to lbl t) u /\
     fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
       stk PG (entry_prov fn (jump_to lbl s) G)
       (entry_taint_vars fn (jump_to lbl s) tn) fn s1 lo u ts` by
    (irule fmp_stage_block_entry >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[MEM]) >>
  `u = t3` by
    (fs[enters_block_def] >> gvs[]) >>
  qexistsl_tac [`entry_prov fn (jump_to lbl s) G`,
    `entry_taint_vars fn (jump_to lbl s) tn`, `inst`, `s1`] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  irule (cj 3 frame_reachable_rules) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[jump_to_halted]
QED
