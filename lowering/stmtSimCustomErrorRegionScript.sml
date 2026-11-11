(* Original-function PC closure from literal control-target certificates. *)
Theory stmtSimCustomErrorRegion
Ancestors
  fragGasPathMem fragExec venomExecSemantics venomInstProofs venomInst
  venomState list

Theorem custom_error_pc_region_closed:
  !Q func.
    (!label index bb inst.
      Q label index /\ lookup_block label func.fn_blocks = SOME bb /\
      get_instruction bb index = SOME inst ==>
      inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
      ((~is_terminator inst.inst_opcode /\ Q label (SUC index)) \/
       (?target block. inst.inst_opcode = JMP /\
         inst.inst_operands = [Label target] /\ Q target 0 /\
         lookup_block target func.fn_blocks = SOME block /\
         phi_prefix_length block.bb_instructions = 0) \/
       (?cond yes no. inst.inst_opcode = JNZ /\
         inst.inst_operands = [cond; Label yes; Label no] /\
         (!target. MEM target [yes;no] ==>
           Q target 0 /\ ?block.
             lookup_block target func.fn_blocks = SOME block /\
             phi_prefix_length block.bb_instructions = 0)) \/
       inst.inst_opcode = REVERT)) ==>
    !ctx u n v. Q u.vs_current_bb u.vs_inst_idx /\
      gas_path_mem_edge ctx func u n (OK v) ==>
      Q v.vs_current_bb v.vs_inst_idx
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_path_mem_edge _ _ _ _ _` mp_tac >>
  simp_tac std_ss [gas_path_mem_edge_def, exit_result_def] >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  (all_tac >>~- ([`exit_result _`], metis_tac[exit_result_def])) >>
  TRY (drule_all step_preserves_control_flow >> simp[] >> NO_TAC) >>
  gvs[is_terminator_def] >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac [step_inst_base_def] >>
  asm_rewrite_tac [] >>
  simp[] >> strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  gvs[jump_to_def, eval_phis_no_phi, AllCaseEqs()] >>
  first_x_assum (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_current_bb`) >>
  simp[] >> strip_tac >> gvs[]
QED
