(* Advance a nonterminator using only the selected INVOKE outcomes. *)
Theory symBodyAdvanceOwn
Ancestors
  symBodyOrdinaryOwn symBodyStaticFacts fnBlockBody fnBlockBodyClasses
  fnBlockBodySteps venomInstProps

Theorem sym_body_nonterm_prefix_selected_own:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  (inst.inst_opcode = LOG ==>
    ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
  step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss /\
  (inst.inst_opcode = INVOKE ==>
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
          sym_terminal (sym_steps_mode allow_own prog env own n ss))) ==>
  ?prefix' rest' ps' vs' as1 ss1 n.
    body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix' rest' (SUC k) ps' pc0 vs' as1 Inv
      ra pc_ret rest mem0 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1 /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    block_rest fuel ctx fn bb vs = block_rest fuel ctx fn bb vs' /\
    vs'.vs_call_ctx = vs.vs_call_ctx /\ vs'.vs_code = own
Proof
  strip_tac >>
  `sym_data_label prog env "code_end"` by
    (irule symBodyStaticFactsTheory.codegen_sym_code_end_label >>
     gvs[body_inv_reloc_def] >> metis_tac[]) >>
  `(MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label prog env "runtime_begin")` by
    (strip_tac >> drule_all body_inv_inst_reloc >> strip_tac >>
     qhdtm_x_assum `body_inv_reloc` mp_tac >>
     simp_tac (srw_ss()) [body_inv_reloc_def] >> strip_tac >>
     irule symBodyStaticFactsTheory.codegen_sym_runtime_begin_label >>
     asm_simp_tac bool_ss [] >>
     qexistsl [`fn`, `inst`, `rpolicy`, `unit`] >> simp[] >>
     metis_tac[listTheory.MEM_EL]) >>
  `?ops ps' rest' n as1 ss1.
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
      ps' = SOME (rest', ps_after) /\ rest_ops = ops ++ rest' /\
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps' vs1 as1 /\
    as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps' as1 ss1` by
    (Cases_on `inst.inst_opcode = INVOKE`
     >- (qpat_x_assum `inst.inst_opcode = INVOKE ==> _` mp_tac >>
         simp[] >> strip_tac >> qexistsl [`ops`, `ps'`, `rest'`, `n`, `as1`, `ss1`] >> simp[]) >>
     Cases_on `inst.inst_opcode = GAS`
     >- (drule_all sym_body_gas_ok_own_kernel >> metis_tac[]) >>
     drule_all sym_body_ordinary_ok_own_kernel >> metis_tac[]) >>
  drule_all body_inv_advance_reloc >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_reloc_def] >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all block_rest_advance >> strip_tac >>
  `vs1.vs_code = vs.vs_code` by metis_tac[step_preserves_code] >>
  `vs1.vs_call_ctx = vs.vs_call_ctx` by metis_tac[step_preserves_call_ctx] >>
  qexistsl [`prefix_ops ++ ops`, `rest'`, `ps'`,
    `vs1 with vs_inst_idx := SUC k`, `as1`, `ss1`, `n`] >> simp[]
QED
