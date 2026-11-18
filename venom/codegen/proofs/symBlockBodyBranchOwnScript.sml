(* Relocated body branches: fold the checked branch outcomes into the body API. *)
Theory symBlockBodyBranchOwn
Ancestors
  symBlockBodyResultOwn symBodyJumpContinueOwn symBodyAdvanceOwn
  symBodyResultBranchesOwn symBodyInvokeOwn symBodyOwnClient
  symBlockBody symBodyStaticFacts fnBlockBodySteps fnBlockBody fnBlockBodyHelpers

Theorem sym_body_jump_continue_own:
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
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  rewrite_tac[sym_body_result_own_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE sym_body_jump_continue_minimal_own)
QED

Theorem sym_body_jmp_step_own:
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
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  rewrite_tac[sym_body_result_own_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE sym_body_jmp_step_minimal_own)
QED

Theorem sym_body_jnz_step_own:
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
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  rewrite_tac[sym_body_result_own_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE sym_body_jnz_step_minimal_own)
QED

(* Discharge the selected INVOKE premise without any frame simulation hypothesis. *)
fun selected_invoke_tac g =
  (strip_tac >>
   `invoke_operands_wf inst` by
     (drule_all body_inv_inst_reloc >> strip_tac >>
      gvs[stackPlanGenTheory.codegen_ready_inst_def]) >>
   drule_then assume_tac invoke_operands_wf_shape_kernel >>
   drule_all sym_body_invoke_step_own_kernel >> simp[]) g

Theorem sym_body_nonterm_prefix_own:
  gen_fn_sim_at_simple_reloc fuel /\ sym_fn_sim_at_own allow_own fuel /\
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
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
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
  strip_tac >> drule sym_body_nonterm_prefix_selected_own >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (qspec_then `allow_own` mp_tac) >>
  (impl_tac >- (simp[] >> selected_invoke_tac)) >> simp[]
QED

Theorem sym_body_out_of_range_own:
  LENGTH bb.bb_instructions <= vs.vs_inst_idx ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  strip_tac >> drule fnBlockBodyHelpersTheory.exec_block_out_of_range >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  drule block_rest_error >> simp[sym_body_result_error_own]
QED

Theorem sym_body_terminator_own:
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
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rewrite_tac[sym_body_result_own_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE sym_body_terminator_minimal_own)
QED

Theorem sym_body_nonok_own:
  gen_fn_sim_at_simple_reloc fuel /\ sym_fn_sim_at_own allow_own fuel /\
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
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rewrite_tac[sym_body_result_own_def] >> strip_tac >>
  drule (BETA_RULE sym_body_nonok_selected_own) >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >>
  disch_then (qspec_then `allow_own` mp_tac) >>
  (impl_tac >- (simp[] >> selected_invoke_tac)) >> simp[]
QED

Theorem sym_body_revert_result_own:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\ revert_forward_pair bb k j /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rewrite_tac[sym_body_result_own_def] >>
  MATCH_ACCEPT_TAC (BETA_RULE sym_body_revert_result_minimal_own)
QED

Theorem sym_body_nonterm_result_own:
  (!m. m < d ==>
    !k prefix_ops rest_ops ps vs as ss.
      m = LENGTH bb.bb_instructions - k /\
      gen_fn_sim_at_simple_reloc fuel /\ gen_fn_frame_sim_at_simple_reloc fuel /\
      sym_fn_sim_at_own allow_own fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
      body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
        growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
        block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
        ra pc_ret rest mem0 /\
      (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
      code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
      (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
      asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
      sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
      sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
        as ss (block_rest fuel ctx fn bb vs)) /\
  d = LENGTH bb.bb_instructions - k /\
  gen_fn_sim_at_simple_reloc fuel /\ sym_fn_sim_at_own allow_own fuel /\
  gen_fn_frame_sim_at_simple_reloc fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
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
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  sym_body_result_own allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rewrite_tac[sym_body_result_own_def] >> strip_tac >>
  drule (SRULE [pairTheory.FORALL_PROD] sym_body_own_nonterm_application) >>
  disch_then (drule_at (Pat `body_inv_reloc`)) >>
  disch_then (drule_at (Pat `sym_frame_inv_own`)) >> simp[]
QED
