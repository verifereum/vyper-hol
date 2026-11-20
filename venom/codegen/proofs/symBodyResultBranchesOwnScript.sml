(* Expanded body-result interfaces for non-OK and revert-forward branches. *)
Theory symBodyResultBranchesOwn
Ancestors
  symBodyTerminalOwn symBodyStaticFacts fnBlockBody fnBlockBodySteps

(* Parse-time abbreviation for the three expanded result clauses. *)
val _ = Parse.temp_overload_on ("result_body_clauses",
  ``\allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 as ss res.
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\
               sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
               asm_sym_rel_own lo prog env own as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))``);

Theorem sym_body_nonok_selected_own:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  (!j. ~revert_forward_pair bb k j) /\ LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = res /\ (!s. res <> OK s) /\
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
  result_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  `MEM (AsmLabel "revert") prog` by
    (drule body_inv_facts_reloc >> strip_tac >>
     drule_all symBodyStaticFactsTheory.placed_revert_sym_code_label >> simp[]) >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_reloc_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all block_rest_other >> disch_then (qspec_then `fn` SUBST1_TAC) >>
  `inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog` by simp[] >>
  Cases_on `res` >> simp[]
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (qpat_x_assum `inst.inst_opcode = INVOKE ==> _` mp_tac >> simp[] >> metis_tac[]) >>
      drule_all sym_body_halt_step_own_kernel >> simp[])
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (qpat_x_assum `inst.inst_opcode = INVOKE ==> _` mp_tac >> simp[] >> metis_tac[]) >>
      drule_all sym_body_abort_step_own_kernel >> simp[]) >>
  drule_all sym_body_ret_step_own_kernel >> simp[]
QED

Theorem sym_body_revert_result_minimal_own:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  result_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  `MEM (AsmLabel "revert") prog` by
    (drule body_inv_facts_reloc >> strip_tac >>
     drule_all symBodyStaticFactsTheory.placed_revert_sym_code_label >> simp[]) >>
  drule_all sym_body_revert_step_own_kernel >>
  disch_then (qspec_then `fuel` mp_tac) >> simp_tac (srw_ss()) [] >> strip_tac >>
  Cases_on `exec_block fuel ctx bb vs` >> gvs[block_rest_def] >> metis_tac[]
QED
