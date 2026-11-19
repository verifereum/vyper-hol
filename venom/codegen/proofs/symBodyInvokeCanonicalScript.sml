(* Canonical body INVOKE is a local-contract instance of the shared producer. *)
Theory symBodyInvokeCanonical
Ancestors
  symBodyInvokePointwise symBodyStaticFacts symFrameInvokeSupport
  symInvokeEntryOwn
  symFrameBoundaryPairing[qualified,ignore_grammar] asmOwnCodeInvariant fnBlockBodySteps fnBlockBodyClasses
  codegenSymRel asmSymBridge asmSymOwnStep

Theorem sym_body_invoke_step_canonical_kernel:
  gen_fn_sim_at_simple fuel /\ sym_fn_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = INVOKE /\ LENGTH (compute_operands inst) <= 16 /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss ==>
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
        sym_steps prog env n ss = SymOK ss1 /\
        sym_frame_inv prog env ctx cpl fn ret srest labs0 ps' as1 ss1) /\
    (!vs1. step_inst fuel ctx inst vs = Halt vs1 ==>
      ?n as1. asm_steps lo o2pc prog n as = AsmHalt as1 /\
        venom_asm_terminal_rel vs1 as1 /\ sym_terminal (sym_steps prog env n ss)) /\
    (!a vs1. step_inst fuel ctx inst vs = Abort a vs1 ==>
      ?n as1. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as1) \/
               (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as1)) /\
        venom_asm_terminal_rel vs1 as1 /\ sym_terminal (sym_steps prog env n ss))
Proof
  strip_tac >>
  drule body_inv_facts >> strip_tac >>
  drule_all body_inv_inst >> strip_tac >>
  `?nm arg_ops. inst.inst_operands = Label nm :: arg_ops` by
    (irule symBodyStaticFactsTheory.invoke_operands_wf_shape >>
     gvs[stackPlanGenTheory.codegen_ready_inst_def]) >>
  drule (iffLR body_inv_reloc_specialize) >> strip_tac >>
  qhdtm_assum `body_inv`
    (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `vs.vs_code = as.as_code` by
    gvs[frameRelTheory.fn_frame_inv_def, contextCodegenRelTheory.context_venom_asm_rel_def,
        frameRelTheory.frame_view_def] >>
  `asm_data_env_lo_ok lo prog env as.as_code` by
    gvs[sym_frame_inv_def, asm_sym_rel_def, asm_data_env_lo_ok_canonical] >>
  `sym_frame_inv_own lo prog env as.as_code ctx cpl fn ret srest labs0 ps as ss` by
    gvs[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >>
  drule_at (Pos (el 3))
    (sym_body_invoke_step_pointwise |>
      Q.INST [`allow_own` |-> `F`, `own` |-> `as.as_code`] |>
      SRULE [sym_steps_mode_def]) >>
  disch_then (drule_at (Pat `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`inst`, `fuel`] mp_tac) >>
  (impl_tac >-
    (simp[SF CONJ_ss] >> conj_tac >-
       (rpt gen_tac >> strip_tac >> irule body_callee_sim >>
        rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
     rpt gen_tac >> strip_tac >>
     gvs[asm_sym_rel_own_canonical] >>
     drule_at (Pat `setup_callee _ _ _ = _`)
       symFrameInvokeSupportTheory.sym_invoke_callee_sim >>
     disch_then (drule_at (Pat `fn_entry_state_rel _ _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
     disch_then (drule_at (Pat `sym_fn_sim_at _`)) >>
     disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
     disch_then (drule_at (Pat `asm_sym_rel _ _ _ _`)) >>
     disch_then (drule_at (Pat `FLOOKUP _ (w2n _) = SOME _`)) >>
     disch_then (qspecl_then
       [`SND (compute_label_offsets prog)`, `j`, `EL j cpl.cp_regions`,
        `ret_lbl`, `csrest`] mp_tac) >>
     simp[SF CONJ_ss] >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!rv vs'. run_blocks _ _ _ _ = IntRet rv vs' ==> _` drule >>
     strip_tac >>
     drule asm_steps_code_preserved >> strip_tac >>
     rpt (goal_assum (drule_at Any)) >> simp[])) >>
  simp[symFrameBoundaryPairingTheory.sym_frame_inv_canonical_own] >> strip_tac >>
  qexistsl [`ops`, `ps'`, `rest'`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!vs1. step_inst _ _ _ _ = OK vs1 ==> _` drule >>
  strip_tac >> rpt (goal_assum (drule_at Any)) >> simp[]
QED
