Theory fnStaticAbortBody
Ancestors
  fnStaticAbortJump fnStaticAbortInvoke fnStaticAbortInstSteps
  fnStaticAbortBodyFacts fnStaticAbortBoundary fnBlockBody fnBlockBodySteps
  fnBlockBodyHelpers unitShapeDefs
  staticAbortExec staticAbortDefs venomExecSemantics venomExecProps
  venomInst venomWf rich_list

Theorem block_body_frame_sim_abort:
  !d k prefix_ops rest_ops ps vs ast.
  d = LENGTH bb.bb_instructions - k /\
  gen_fn_sim_abort_at fuel /\ gen_fn_frame_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
    ra pc_ret rest mem0 ==>
  body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast
    (block_rest fuel ctx fn bb vs)
Proof
  completeInduct_on `d` >> rpt gen_tac >> strip_tac >>
  Cases_on `in_static_abort_prefix fn vs`
  >- (drule_all body_inv_abort_pending >> strip_tac >>
      `vs.vs_call_ctx.cc_static /\ static_abort_at bb vs.vs_inst_idx` by
        (fs[body_inv_abort_def, in_static_abort_prefix_def] >> gvs[]) >>
      `(!t. exec_block fuel ctx bb vs <> OK t) /\
       (!ret t. exec_block fuel ctx bb vs <> IntRet ret t) /\
       (!t. exec_block fuel ctx bb vs <> Halt t)` by
        metis_tac[static_abort_at_no_normal, static_abort_at_no_halt] >>
      pure_rewrite_tac[block_rest_def] >>
      Cases_on `exec_block fuel ctx bb vs` >>
      gvs[body_result_abort_def] >>
      metis_tac[static_abort_at_abort_requests]) >>
  drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  reverse (Cases_on `k < LENGTH bb.bb_instructions`)
  >- (`vs.vs_inst_idx = k` by fs[body_inv_abort_def] >>
      `?e. exec_block fuel ctx bb vs = Error e` by
        (irule fnBlockBodyHelpersTheory.exec_block_out_of_range >> simp[]) >>
      drule block_rest_error >> disch_then (qspec_then `fn` SUBST1_TAC) >>
      simp[body_result_abort_def]) >>
  qabbrev_tac `inst = EL k bb.bb_instructions` >>
  `EL k bb.bb_instructions = inst` by simp[Abbr `inst`] >>
  drule_all body_plan_inv_inst >> strip_tac >>
  `vs.vs_inst_idx = k` by fs[body_inv_abort_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by simp[] >>
  `LENGTH (compute_operands inst) <= 16` by metis_tac[body_operands_le_16] >>
  `inst.inst_opcode = LOG ==>
   ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4` by
    metis_tac[body_log_topics, log_case_topics] >>
  Cases_on `?j. revert_forward_pair bb k j`
  >- (pop_assum strip_assume_tac >>
      qhdtm_assum `body_plan_inv`
        (strip_assume_tac o REWRITE_RULE [body_plan_inv_def]) >>
      drule_all body_plan_inv_static >> strip_tac >>
      `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
       DROP k bb.bb_instructions` by simp[DROP_DROP_T] >>
      `!off. ~MEM (SORestore off) rest_ops /\ ~MEM (SOSpill off) rest_ops` by
        (qpat_x_assum `!j. revert_forward_pair bb k j ==> !ops ps_end. _`
           drule >> disch_then (qspecl_then [`rest_ops`, `ps_after`] mp_tac) >>
         gvs[]) >>
      drule_all body_abort_revert_step >>
      disch_then (qspec_then `fuel` mp_tac) >>
      POP_ASSUM_LIST (K all_tac) >> strip_tac >>
      pure_rewrite_tac[block_rest_def] >>
      Cases_on `exec_block fuel ctx bb vs` >> gvs[]) >>
  `!j. ~revert_forward_pair bb k j` by metis_tac[] >>
  `~in_revert_forward fn vs` by
    (qhdtm_assum `body_inv_abort`
       (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
     gvs[contextCodegenRelTheory.in_revert_forward_def,
         contextCodegenRelTheory.revert_forward_at_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!i j. revert_forward_pair bb i j ==> _` drule >>
     fs[contextCodegenRelTheory.revert_forward_pair_def]) >>
  Cases_on `step_inst fuel ctx inst vs`
  >~ [`step_inst fuel ctx inst vs = OK vs1`]
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (drule_all step_ok_terminator_jump >> strip_tac
          >~ [`inst.inst_opcode = DJMP`]
          >- (fs[inst_shape_ok_def])
          >~ [`inst.inst_opcode = JMP`]
          >- (drule_all body_abort_jmp_step >> strip_tac >>
              drule_all block_rest_jump >> disch_then (qspec_then `fn` SUBST1_TAC) >> simp[])
          >~ [`inst.inst_opcode = JNZ`]
          >- (drule_all body_abort_jnz_step >> strip_tac >>
              drule_all block_rest_jump >> disch_then (qspec_then `fn` SUBST1_TAC) >> simp[])) >>
      `?ops ps' rest' n ast1.
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
         ast1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)` by
        (Cases_on `inst.inst_opcode = INVOKE`
         >- (drule_all body_abort_invoke_step >> simp[]) >>
         Cases_on `inst.inst_opcode = GAS`
         >- (drule_all body_abort_gas_ok >> simp[]) >>
         drule_all body_abort_ordinary_ok >> simp[]) >>
      drule_all body_inv_abort_advance >> strip_tac >>
      qpat_x_assum `!m. m < d ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC k` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`SUC k`, `prefix_ops ++ ops`, `rest'`, `ps'`,
                               `vs1 with vs_inst_idx := SUC k`, `ast1`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      drule_all block_rest_advance >> disch_then (qspec_then `fn` SUBST1_TAC) >>
      asm_rewrite_tac[] >> irule body_result_abort_prefix >>
      qexistsl [`ast1`, `n`] >> simp[])
  >~ [`step_inst fuel ctx inst vs = Halt vs1`]
  >- (drule block_rest_other >> disch_then drule >> simp[] >>
      disch_then (qspec_then `fn` SUBST1_TAC) >> Cases_on `inst.inst_opcode = INVOKE`
      >- (drule_all body_abort_invoke_step >> simp[]) >>
      drule_all body_abort_halt_step >> simp[])
  >~ [`step_inst fuel ctx inst vs = Abort a vs1`]
  >- (drule block_rest_other >> disch_then drule >> simp[] >>
      disch_then (qspec_then `fn` SUBST1_TAC) >> Cases_on `inst.inst_opcode = INVOKE`
      >- (drule_all body_abort_invoke_step >> simp[]) >>
      drule_all body_abort_abort_step >> simp[])
  >~ [`step_inst fuel ctx inst vs = IntRet ret vs1`]
  >- (drule block_rest_other >> disch_then drule >> simp[] >>
      disch_then (qspec_then `fn` SUBST1_TAC) >> drule_all body_abort_ret_step >> simp[])
  >~ [`step_inst fuel ctx inst vs = Error e`]
  >- (drule block_rest_other >> disch_then drule >> simp[] >>
      disch_then (qspec_then `fn` SUBST1_TAC) >> simp[body_result_abort_def])
QED
