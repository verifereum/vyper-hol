(* Terminal body branches, below the body-result owner. *)
Theory symBodyTerminalOwn
Ancestors
  symControlTerminalDischargeOwn symControlRetDischargeOwn
  symControlForwardDischargeOwn fnBlockBodySteps fnBlockBodyClasses
  codegenSymRel codegenSymOwnRel unitShapeDefs

(* A quotation abbreviation only: the exact three body-result clauses.
   No logical constant is introduced, and the body owner is not imported. *)
val _ = Parse.temp_overload_on ("terminal_body_clauses",
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

Theorem sym_body_halt_step_own_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Halt vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  terminal_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs1)
Proof
  strip_tac >> simp[] >>
  drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all body_inv_step_reloc >> strip_tac >>
  drule_all body_inv_static_reloc >> strip_tac >>
  drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all body_inv_not_in_rf_reloc >> strip_tac >>
  drule_all body_inv_memory_reloc >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_inv_label_resolve_reloc >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv_reloc` (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan`) sym_halt_frame_sim_deep_own >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked`)) >>
  simp[] >> disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem sym_body_abort_step_own_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode <> INVOKE /\ (!j. ~revert_forward_pair bb k j) /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = Abort a vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  (inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  terminal_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs1)
Proof
  strip_tac >> simp[] >>
  drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all body_inv_step_reloc >> strip_tac >>
  drule_all body_inv_static_reloc >> strip_tac >>
  drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >> strip_tac >>
  drule_all body_inv_not_in_rf_reloc >> strip_tac >>
  drule_all body_inv_memory_reloc >> strip_tac >>
  `!e. step_inst fuel ctx inst vs <> Error e` by simp[] >>
  drule body_inv_label_resolve_reloc >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qhdtm_assum `body_inv_reloc` (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan`) sym_abort_frame_sim_deep_own >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked`)) >>
  simp[] >> disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem sym_body_ret_step_own_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  LENGTH (compute_operands inst) <= 16 /\
  step_inst fuel ctx inst vs = IntRet rv vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  terminal_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs1)
Proof
  strip_tac >> simp[] >>
  drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all body_inv_step_reloc >> strip_tac >>
  drule_all body_inv_static_reloc >> strip_tac >>
  drule body_inv_equiv_reloc >> disch_then drule >> disch_then drule >> strip_tac >>
  `inst.inst_opcode = RET` by metis_tac[codegen_ready_intret_opcode] >>
  qhdtm_assum `body_inv_reloc` (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (irule fnBlockBodyHelpersTheory.reachable_fn_mem_inst >> simp[] >> metis_tac[]) >>
  `ps'.ps_stack = []` by metis_tac[] >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan`) sym_ret_frame_sim_deep_own >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked`)) >>
  simp[] >> disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem body_inv_rest_placed_reloc_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 ==>
  asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)
Proof
  pure_rewrite_tac [body_inv_reloc_def] >> strip_tac >>
  qpat_x_assum `as.as_pc = _` SUBST1_TAC >>
  irule fnBlockBodyHelpersTheory.block_ops_at >> qexists_tac `[]` >>
  pure_rewrite_tac [listTheory.APPEND_NIL] >>
  qpat_x_assum `block_ops = _` (fn th => rewrite_tac [GSYM th]) >>
  first_assum ACCEPT_TAC
QED

Theorem sym_body_revert_abort_own_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  revert_forward_pair bb k j /\ exec_block fuel ctx bb vs = Abort a vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  MEM (AsmLabel "revert") prog /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  terminal_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs1)
Proof
  strip_tac >> simp[] >> drule body_inv_facts_reloc >> strip_tac >>
  `k < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     gvs[contextCodegenRelTheory.revert_forward_pair_def,
         venomInstTheory.get_instruction_def]) >>
  `EL k bb.bb_instructions = EL k bb.bb_instructions` by simp[] >>
  drule_all body_inv_static_reloc >> strip_tac >>
  `asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp rest_ops)` by
    metis_tac[body_inv_rest_placed_reloc_kernel] >>
  qhdtm_assum `body_inv_reloc` (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `fn_shape_ok fn` by
    (gvs[unit_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!inst. MEM inst bb.bb_instructions ==> inst_shape_ok inst` by
    (rpt strip_tac >> drule_all fnBlockBodyHelpersTheory.body_inst_ready >>
     gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all rf_pair_no_labels >> strip_tac >>
  `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
   DROP k bb.bb_instructions` by simp[rich_listTheory.DROP_DROP_T] >>
  `generate_block_insts_plan liveness dfg cfg fn bb.bb_label
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (k - LENGTH (get_params bb.bb_instructions))
    (DROP k bb.bb_instructions) ps = SOME (rest_ops, ps_after)` by metis_tac[] >>
  `!name. MEM (AsmOp name) (execute_plan cpl.cp_initial_fmp rest_ops) ==>
    IS_SOME (evm_opcode_byte name)` by metis_tac[body_placed_target_safe] >>
  qpat_x_assum `!j. revert_forward_pair bb k j ==> !k' inst' op. _` drule >> strip_tac >>
  qpat_x_assum `!j. revert_forward_pair bb k j ==> !ops ps_end. _` drule >>
  disch_then drule >> strip_tac >>
  drule_at (Pat `fn_frame_inv`) sym_revert_forward_frame_sim_deep_own >>
  disch_then (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked`)) >>
  simp[] >> disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem sym_body_revert_step_own_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  MEM (AsmLabel "revert") prog /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  terminal_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (exec_block fuel ctx bb vs)
Proof
  strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_reloc_def] >>
  `revert_forward_pair bb vs.vs_inst_idx j` by metis_tac[] >>
  drule fnBlockBodyClassesTheory.rf_exec_block_cases >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >> strip_tac
  >- (simp[] >> drule_all sym_body_revert_abort_own_kernel >> simp[]) >>
  simp[]
QED
