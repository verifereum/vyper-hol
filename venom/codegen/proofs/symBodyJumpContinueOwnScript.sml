(* Minimal frame-only interfaces for reached jumps and terminators. *)
Theory symBodyJumpContinueOwn
Ancestors
  symBodyJumpOwn symBodySuccessorPointwise symBodyStaticFacts
  symFnSimSpec fnBlockBody fnBlockBodyClasses fnBlockBodySteps fnBlockBodyHelpers

(* Parse-time abbreviation for the three expanded result clauses. *)
val _ = Parse.temp_overload_on ("jump_body_clauses",
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

Theorem sym_body_jump_continue_minimal_own:
  gen_fn_frame_sim_at_simple_reloc fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps_after as1 ss1 ==>
  ~vs1.vs_halted /\
  jump_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all_then assume_tac body_jump_entry_reloc_kernel >>
  qpat_x_assum `vs1 = jump_to t vs` SUBST_ALL_TAC >>
  drule (BETA_RULE sym_body_jump_continue_pointwise) >> disch_then irule >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
  reverse conj_tac >- gns[] >>
  rpt gen_tac >> strip_tac >>
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `!l. FLOOKUP (jump_to t vs).vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)` by metis_tac[] >>
  qhdtm_x_assum `sym_fn_frame_sim_at_own` mp_tac >>
  rewrite_tac[sym_fn_frame_sim_at_own_def] >>
  disch_then irule >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  conj_tac >- gns[] >>
  conj_tac >- (qexistsl [`rpolicy`, `unit`] >> gns[]) >>
  conj_tac >- (qexists `Inv` >> gns[]) >>
  qexistsl [`tops`, `i`, `lbl_ctr`,
    `ps_tdfs with <|ps_stack := ps_after.ps_stack; ps_spilled := ps_after.ps_spilled|>`,
    `ps_tdfs`, `tafter`, `ps_end`, `ra`, `ret`] >> gns[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem sym_body_jmp_step_minimal_own:
  gen_fn_frame_sim_at_simple_reloc fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ~vs1.vs_halted /\
  jump_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all symBodyStaticFactsTheory.jmp_wf_operands >> disch_then assume_tac >>
  `is_terminator inst.inst_opcode` by simp[venomInstTheory.is_terminator_def] >>
  `!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog` by
    (rpt strip_tac >> assume_tac symBodyStaticFactsTheory.placed_nonentry_sym_code_label >>
     drule_all body_succ_sym_label_reloc_kernel >> strip_tac >> simp[]) >>
  drule_all sym_body_jmp_prefix_own_kernel >> strip_tac >>
  drule_all (BETA_RULE sym_body_jump_continue_minimal_own) >> simp[]
QED

Theorem sym_body_jnz_step_minimal_own:
  gen_fn_frame_sim_at_simple_reloc fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ~vs1.vs_halted /\
  jump_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule body_inv_facts_reloc >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  drule_all symBodyStaticFactsTheory.jnz_wf_operands >> disch_then assume_tac >>
  `is_terminator inst.inst_opcode` by simp[venomInstTheory.is_terminator_def] >>
  `!c l1 l2. inst.inst_operands = [c;Label l1;Label l2] ==>
    eval_operand c vs = eval_operand c (frame_view fn ra vs)` by
    metis_tac[symBodyStaticFactsTheory.jnz_condition_frame_view] >>
  `!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog` by
    (rpt strip_tac >> assume_tac symBodyStaticFactsTheory.placed_nonentry_sym_code_label >>
     drule_all body_succ_sym_label_reloc_kernel >> strip_tac >> simp[]) >>
  drule_all sym_body_jnz_prefix_own_kernel >> strip_tac >>
  drule_all (BETA_RULE sym_body_jump_continue_minimal_own) >> simp[]
QED

Theorem sym_body_terminator_minimal_own:
  gen_fn_frame_sim_at_simple_reloc fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  jump_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all body_inv_inst_reloc >> strip_tac >>
  `vs.vs_inst_idx = k` by gvs[body_inv_reloc_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule_all step_ok_terminator_jump >> strip_tac
  >- (drule_all (BETA_RULE sym_body_jmp_step_minimal_own) >> strip_tac >>
      metis_tac[block_rest_jump])
  >- (drule_all (BETA_RULE sym_body_jnz_step_minimal_own) >> strip_tac >>
      metis_tac[block_rest_jump]) >>
  gvs[unitShapeDefsTheory.inst_shape_ok_def]
QED
