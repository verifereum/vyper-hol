(* Body-level INVOKE planning and synchronized own-mode outcomes. *)
Theory symBodyInvokeOwn
Ancestors
  symFrameInvokeSourceOwn asmSymModeOwn fnBlockBodyClasses fnBlockBodySteps
  symFnSimSpec codegenSymRel unitShapeDefs stackPlanCfgIrrelevance symBodyInvokePointwise

Theorem sym_body_invoke_step_own_kernel:
  gen_fn_sim_at_simple_reloc fuel /\ sym_fn_sim_at_own allow_own fuel /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
  (?nm arg_ops. inst.inst_operands = Label nm :: arg_ops) /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ?ops ps' rest'.
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
    (!vs1. step_inst fuel ctx inst vs = OK vs1 ==>
      ?n as1 ss1.
        asm_steps lo o2pc prog n as = AsmOK as1 /\
        fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
        as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
        sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
        sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
      ?n as1. asm_steps lo o2pc prog n as = AsmHalt as1 /\
        venom_asm_terminal_rel vs1 as1 /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
      ?n as1. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as1) \/
               (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as1)) /\
        venom_asm_terminal_rel vs1 as1 /\
        sym_terminal (sym_steps_mode allow_own prog env own n ss))
Proof
  strip_tac >>
  drule_at (Pos (el 3)) sym_body_invoke_step_pointwise >>
  disch_then irule >> simp[SF CONJ_ss] >>
  conj_tac >-
    (qhdtm_assum `body_inv_reloc`
       (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
     rpt gen_tac >> strip_tac >> irule body_callee_sim_reloc >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule symFrameInvokeSupportTheory.sym_invoke_callee_sim_own >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
