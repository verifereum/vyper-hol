Theory fnStaticAbortInvoke
Ancestors
  fnStaticAbortSpec fnStaticAbortBodyFacts fnBlockBodyClasses
  fnStaticAbortBoundary fnBlockBodySteps contextCodegenRel
  contextStaticAbortRel codegenRel stackPlanTypes
  fnFrameDeepInvoke fnFrameBoundaryInvoke contextCodegenRelProps
  venomExecSemantics venomExecProps venomInst blockSimHelpers
  genBlockSim list frameRel stackPlanGen planExec

(* Instantiate the conditional fuel hypothesis only at the actual callee
   boundary.  Its normal clauses remain the canonical full relations. *)
Theorem body_abort_callee_sim:
  gen_fn_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\
  setup_callee callee args vs = SOME cvs /\
  j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
  MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
  asm_block_at prog cas.as_pc
    (execute_plan cpl.cp_initial_fmp (EL j cpl.cp_regions).sr_plan) /\
  LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
  fn_entry_state_rel cpl callee cvs cas cra crest /\
  (fn_has_retpc callee ==> FLOOKUP o2pc (w2n cra) = SOME cpc) ==>
  (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
     ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
             venom_asm_terminal_rel vs' as') /\
  (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
     ?n as'. (asm_steps lo o2pc prog n cas = AsmRevert as' \/
              asm_steps lo o2pc prog n cas = AsmFault as') /\
             as'.as_requests = vs'.vs_requests) /\
  (!ret vs'. run_blocks fuel ctx callee cvs = IntRet ret vs' ==>
     ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
             as'.as_pc = cpc /\
             as'.as_stack = REVERSE ret.iret_values ++ crest /\
             fn_return_state_rel ctx cpl callee vs' cas as')
Proof
  strip_tac >>
  drule body_inv_abort_plan >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  `active_inst fn inst vs` by
    (fs[body_inv_abort_def, active_inst_def, get_instruction_def] >>
     metis_tac[lookup_block_label]) >>
  `Inv ctx fn inst vs` by
    (fs[body_inv_abort_def] >> metis_tac[]) >>
  `decode_invoke inst = SOME (nm,arg_ops)` by simp[decode_invoke_def] >>
  qhdtm_assum `body_inv_abort`
    (strip_assume_tac o REWRITE_RULE [body_inv_abort_def]) >>
  drule_all reachability_closed_callee >> strip_tac >>
  `!l. FLOOKUP cvs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)` by
    (qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
     rw[setup_callee_def] >> gvs[AllCaseEqs()]) >>
  qhdtm_x_assum `gen_fn_sim_abort_at`
    (mp_tac o REWRITE_RULE [gen_fn_sim_abort_at_def]) >>
  disch_then irule >>
  simp[] >> metis_tac[]
QED

(* Shared call preparation: structural entry, actual smaller-fuel boundary,
   and the concrete prefix taking the caller into that boundary. *)
val abort_call_enter_tac =
  drule_all body_plan_call_entry >> strip_tac >>
  `fn_has_retpc callee ==>
     FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
       SOME (ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3)` by
    simp[] >>
  drule_all body_abort_callee_sim >> strip_tac >>
  `asm_steps lo o2pc prog
     (LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3) ast =
   AsmOK cas` by
    (irule asm_steps_compose_ok >> qexists `mid` >>
     conj_tac >> first_assum ACCEPT_TAC);

Theorem body_invoke_abort_terminal:
  gen_fn_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  LENGTH (compute_operands inst) <= 16 ==>
  (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast (Halt vs1)) /\
  (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast (Abort a vs1))
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> drule_all invoke_source_halt >> strip_tac >>
      abort_call_enter_tac >>
      qpat_x_assum `!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==> _`
        drule >> strip_tac >>
      simp[body_result_abort_def] >>
      metis_tac[asm_steps_compose_halt]) >>
  rpt strip_tac >> drule_all invoke_source_abort >> strip_tac >>
  abort_call_enter_tac >>
  qpat_x_assum `!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==> _`
    drule >> strip_tac >>
  simp[body_result_abort_def] >>
  metis_tac[asm_steps_compose_revert, asm_steps_compose_fault]
QED

Theorem body_invoke_abort_ok:
  gen_fn_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = OK vs1 ==>
  ?ops ps' rest' n as1.
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
    asm_steps lo o2pc prog n ast = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)
Proof
  strip_tac >> drule body_inv_abort_plan >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  drule_all body_plan_inv_step >> strip_tac >>
  drule_all invoke_source_ok >> strip_tac >> abort_call_enter_tac >>
  qpat_x_assum `!ret vs'. run_blocks fuel ctx callee cvs = IntRet ret vs' ==> _`
    drule >> strip_tac >>
  rename1 `asm_steps lo o2pc prog n cas = AsmOK asr` >>
  drule_all invoke_plan_decompose >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`EL k bb.bb_instructions = inst`, `EL j ctx.ctx_functions = callee`] >>
  gvs[] >>
  `codegen_context_obligations (\_ _ _ _. F) ctx cpl /\
   MEM fn.fn_name (fcg_analyze ctx).fcg_reachable` by
    fs[body_plan_inv_def] >>
  `~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name` by
    (drule_all invoke_context_no_cycle >> simp[]) >>
  `ordered_spill_regions cpl.cp_regions /\ ctx_wf ctx` by
    fs[codegen_context_obligations_def, context_plan_layout_wf_def] >>
  `fn_directly_calls ctx fn.fn_name callee.fn_name` by
    metis_tac[invoke_direct_call] >>
  drule_all invoke_entry_structural_marked >> strip_tac >>
  `ALL_DISTINCT inst.inst_outputs` by
    metis_tac[codegen_ready_inst_outputs_distinct] >>
  `EVERY (\x. ~retpc_var fn x) inst.inst_outputs` by
    (simp[EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     irule frameViewFactsTheory.noncopy_output_not_retpc >>
     conj_tac >- fs[codegen_ready_fn_def] >> qexists `inst` >> simp[]) >>
  `fn_return_state_rel ctx cpl callee rvs mid asr` by
    (qpat_x_assum `fn_return_state_rel _ _ _ _ _ asr` mp_tac >>
     simp[fn_return_state_rel_def]) >>
  `asm_block_at prog asr.as_pc
     (execute_plan cpl.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))` by
    (`asr.as_pc = ast.as_pc +
       LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3` by simp[] >>
     pop_assum SUBST1_TAC >> irule invoke_return_block >>
     qexists `callee.fn_name` >> simp[]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
     | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts)` by
    simp[EVERY_APPEND] >>
  drule_all (SRULE [] invoke_return_frame_numeric_exact) >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexistsl [`LENGTH (execute_plan cpl.cp_initial_fmp (iops ++ rops)) + 3 + n +
    (1 + LENGTH (execute_plan cpl.cp_initial_fmp (pops ++ opts)))`, `fin`] >>
  conj_tac >-
    (map_every (fn q => qpat_x_assum q mp_tac)
       [`asm_steps lo o2pc prog _ ast = AsmOK cas`,
        `asm_steps lo o2pc prog n cas = AsmOK asr`,
        `asm_steps lo o2pc prog _ asr = AsmOK fin`] >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[asm_steps_compose_ok]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  fs[execute_plan_def, exec_stack_op_def]
QED

Theorem body_abort_invoke_step:
  gen_fn_sim_abort_at fuel /\
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 ==>
  (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
    ?ops ps' rest' n as1.
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
      asm_steps lo o2pc prog n ast = AsmOK as1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
      as1.as_pc = ast.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops)) /\
  (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast (Halt vs1)) /\
  (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast (Abort a vs1))
Proof
  strip_tac >>
  `codegen_ready_inst inst` by
    (drule body_inv_abort_plan >> strip_tac >>
     drule_all body_plan_inv_inst >> simp[]) >>
  `?nm arg_ops. inst.inst_operands = Label nm :: arg_ops` by
    (qpat_x_assum `codegen_ready_inst inst` mp_tac >>
     qpat_x_assum `inst.inst_opcode = INVOKE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rw[codegen_ready_inst_def, invoke_operands_wf_def] >>
     Cases_on `inst.inst_operands` >> gvs[] >>
     rename1 `case op of Lit _ => _ | Var _ => _ | Label _ => _` >>
     Cases_on `op` >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> drule_all body_invoke_abort_ok >> simp[]) >>
  drule_all body_invoke_abort_terminal >> simp[]
QED
