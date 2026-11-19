(* Canonical clients of the reached-successor simulation. *)
Theory symBodyCanonicalSuccessor
Ancestors
  symBodyCanonicalSelected symBodySuccessorPointwise symBodyJumpPointwise
  symBodyJumpOwn symBodyStaticFacts symFrameBoundaryPairing symFnSimSpec
  fnBlockBody fnBlockBodyHelpers fnBlockBodyClasses fnBlockBodySteps
  asmOwnCodeInvariant asmSymOwnStep codegenSymRel asmSymBridge frameRel
  contextCodegenRel codegenRel venomExecSemantics venomInst venomState

(* Parse-time abbreviation: the canonical clients use the same three clauses. *)
val _ = Parse.temp_overload_on ("jump_clauses",
  ``\steps rel lo o2pc prog cpl ctx fn mem0 pc_ret rest srest labs0 as ss res.
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\ sym_terminal (steps n ss)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\ sym_terminal (steps n ss)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\ steps n ss = SymOK ss' /\ rel as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))``);

Theorem canonical_jump_clauses[local]:
  lo = SND (compute_label_offsets prog) /\ asm_static_wf prog /\ as.as_code = own ==>
  (jump_clauses (sym_steps_mode F prog env own) (asm_sym_rel_own lo prog env own)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest srest labs0 as ss res <=>
   jump_clauses (sym_steps prog env) (asm_sym_rel prog env)
      lo o2pc prog cpl ctx fn mem0 pc_ret rest srest labs0 as ss res)
Proof
  strip_tac >> simp[sym_steps_mode_def, asm_sym_rel_own_canonical] >>
  eq_tac >> strip_tac >> simp[] >> rpt strip_tac >> first_x_assum drule >>
  strip_tac >> qexistsl [`n`, `as'`, `ss'`] >> simp[] >>
  metis_tac[asm_steps_code_preserved]
QED

Theorem sym_body_jump_continue_canonical:
  sym_fn_frame_sim_at fuel /\
  body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
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
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  sym_steps prog env n ss = SymOK ss1 /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps_after as1 ss1 ==>
  ~vs1.vs_halted /\
  jump_clauses (sym_steps prog env) (asm_sym_rel prog env)
    lo o2pc prog cpl ctx fn mem0 pc_ret rest srest labs0 as ss (run_blocks fuel ctx fn vs1)
Proof
  BETA_TAC >> strip_tac >>
  `lo = SND (compute_label_offsets prog) /\
   body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
     growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
     block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
     ra pc_ret rest mem0` by metis_tac[body_inv_reloc_specialize] >>
  `as1.as_code = vs.vs_code` by
    gvs[jump_to_def, fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `as.as_code = vs.vs_code` by metis_tac[asm_steps_code_preserved] >>
  `asm_data_env_lo_ok lo prog env vs.vs_code` by
    gvs[sym_frame_inv_def, asm_data_env_lo_ok_canonical, asm_sym_rel_def] >>
  `sym_frame_inv_own lo prog env vs.vs_code ctx cpl fn ret srest labs0 ps_after as1 ss1` by
    simp[sym_frame_inv_canonical_own] >>
  drule_all_then assume_tac body_jump_entry_reloc_kernel >>
  `~vs1.vs_halted /\
   jump_clauses (sym_steps_mode F prog env vs.vs_code) (asm_sym_rel_own lo prog env vs.vs_code)
     lo o2pc prog cpl ctx fn mem0 pc_ret rest srest labs0 as ss (run_blocks fuel ctx fn vs1)`
    suffices_by (BETA_TAC >> simp[BETA_RULE canonical_jump_clauses]) >>
  BETA_TAC >>
  drule (SRULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`]
    (SPEC_ALL (BETA_RULE sym_body_jump_continue_pointwise)))) >>
  disch_then (drule_at (Pat `_ = jump_to _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `asm_steps _ _ _ _ _ = AsmOK _`)) >>
  disch_then (drule_at (Pat `sym_steps _ _ _ _ = SymOK _`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (drule_at (Pat `FLOOKUP lo _ = SOME _`)) >>
  gns[sym_steps_mode_def] >> (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ ps_after _ _` kall_tac >>
     qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ ps_after _ _` kall_tac >>
     gvs[sym_frame_inv_canonical_own, BETA_RULE (SRULE [sym_steps_mode_def] canonical_jump_clauses)] >>
     qhdtm_assum `sym_fn_frame_sim_at`
       (mp_tac o REWRITE_RULE [sym_fn_frame_sim_at_def]) >>
     disch_then (drule_at (Pat `sym_frame_inv`)) >>
     disch_then (drule_at (Pat `fn_frame_inv`)) >>
     disch_then (drule_at (Pat `generate_block_plan`)) >>
     disch_then (drule_at (Pat `lineage_entry`)) >> disch_then irule >>
     qhdtm_assum `body_inv` (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
     gvs[] >> rpt conj_tac >> metis_tac[])) >>
  simp[sym_steps_mode_def]
QED

val _ = Parse.temp_overload_on ("canonical_jump_site",
  ``body_inv rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
    step_inst fuel ctx inst vs = OK vs1 /\
    label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cpl fn ret srest labs0 ps as ss``);

val _ = Parse.temp_overload_on ("jump_prefix_facts",
  ``\steps frame.
    ?n as1 ss1 t off.
      asm_steps lo o2pc prog n as = AsmOK as1 /\ steps n (ss:sym_state) = SymOK ss1 /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
      frame ps_after as1 ss1 /\
      (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
        operand_val (frame_view fn ra vs1) lo at =
        operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
      is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
      vs1 = jump_to t vs /\
      FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc``);

fun canonical_prefix_tac th =
  drule (REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]
    (Q.INST [`allow_own` |-> `F`] (SPEC_ALL th))) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  gns[] >> metis_tac[];

Theorem sym_body_jump_prefix_canonical:
  canonical_jump_site /\ (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) ==>
  jump_prefix_facts (sym_steps prog env) (sym_frame_inv prog env ctx cpl fn ret srest labs0)
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) >>
  drule_all sym_body_canonical_facts >> strip_tac >>
  drule body_inv_facts >> strip_tac >> drule_all body_inv_inst >> strip_tac >>
  `is_terminator inst.inst_opcode` by metis_tac[is_terminator_def] >>
  `!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog` by
    (rpt strip_tac >> assume_tac symBodyStaticFactsTheory.placed_nonentry_sym_code_label >>
     drule_all body_succ_sym_label_reloc_kernel >> strip_tac >> simp[]) >>
  `jump_prefix_facts (sym_steps prog env)
      (sym_frame_inv_own lo prog env vs.vs_code ctx cpl fn ret srest labs0)` by
    (BETA_TAC >> qpat_x_assum `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ` strip_assume_tac
     >- (drule_all_then assume_tac symBodyStaticFactsTheory.jmp_wf_operands >>
         canonical_prefix_tac sym_body_jmp_prefix_pointwise)
     >- (drule_all_then assume_tac symBodyStaticFactsTheory.jnz_wf_operands >>
         `!c l1 l2. inst.inst_operands = [c;Label l1;Label l2] ==>
            eval_operand c vs = eval_operand c (frame_view fn ra vs)` by
           metis_tac[symBodyStaticFactsTheory.jnz_condition_frame_view] >>
         canonical_prefix_tac sym_body_jnz_prefix_pointwise)) >>
  qexistsl [`n`, `as1`, `ss1`, `t`, `off`] >> gvs[sym_frame_inv_canonical_own] >>
  first_assum ACCEPT_TAC
QED

Theorem sym_body_jump_step_canonical:
  canonical_jump_site /\ sym_fn_frame_sim_at fuel /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) ==>
  ~vs1.vs_halted /\
  jump_clauses (sym_steps prog env) (asm_sym_rel prog env)
    lo o2pc prog cpl ctx fn mem0 pc_ret rest srest labs0 as ss (run_blocks fuel ctx fn vs1)
Proof
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) >>
  drule_all (BETA_RULE sym_body_jump_prefix_canonical) >> strip_tac >>
  drule_all (BETA_RULE sym_body_jump_continue_canonical) >> simp[]
QED

Theorem sym_body_terminator_canonical:
  canonical_jump_site /\ sym_fn_frame_sim_at fuel /\ is_terminator inst.inst_opcode ==>
  jump_clauses (sym_steps prog env) (asm_sym_rel prog env)
    lo o2pc prog cpl ctx fn mem0 pc_ret rest srest labs0 as ss (block_rest fuel ctx fn bb vs)
Proof
  BETA_TAC >> strip_tac >> drule_all body_inv_inst >> strip_tac >>
  `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ` by
    (drule_all step_ok_terminator_jump >> rpt strip_tac >> gvs[unitShapeDefsTheory.inst_shape_ok_def]) >>
  `vs.vs_inst_idx = k` by gvs[body_inv_def] >>
  `get_instruction bb vs.vs_inst_idx = SOME inst` by metis_tac[] >>
  drule (BETA_RULE sym_body_jump_step_canonical) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `sym_frame_inv`)) >> simp[] >> strip_tac >>
  drule_all block_rest_jump >> disch_then (qspec_then `fn` SUBST1_TAC) >> simp[]
QED
