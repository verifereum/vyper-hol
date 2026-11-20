(* Unconditional relocated own-mode forwarded-revert interfaces. *)
Theory symControlForwardDischargeOwn
Ancestors
  symControlForwardContinuationOwn symControlForwardPrepareOwn
  symControlForwardCopyExecutionOwn symControlReplayOwn symControlReorderOwn symFrameControlFacts
  symControlTerminalDischargeOwn asmSymModeOwn asmSymBridge codegenSymRel codegenSymOwnRel

val _ = Parse.temp_overload_on ("rf_B",
  fst (dest_imp (concl sym_rf_assign_plan_execution_mode_conditional)));

Theorem sym_rf_replay_interfaces:
  rf_B
Proof
  rpt conj_tac
  >- ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- ACCEPT_TAC list_rel_op_kind_transport
  >- MATCH_ACCEPT_TAC sym_reorder_one_decompose
  >- MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay_expr
  >- MATCH_ACCEPT_TAC reorder_restore_no_restore_identity
  >- MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity
  >- MATCH_ACCEPT_TAC do_swap_no_restore_shallow
  >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

val own_rf_kernel = SRULE [asm_sym_rel_core_own]
  (Q.INST [`code_ok` |->
    `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
    (SPEC_ALL (MP sym_revert_forward_frame_sim_deep_mode_conditional
      sym_rf_replay_interfaces)));
val _ = Parse.temp_overload_on ("own_rf_C", fst (dest_imp (concl own_rf_kernel)));

Theorem sym_rf_copy_preparation_interface_own:
  code_labels_agree prog lo /\ asm_static_wf prog ==> own_rf_C
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `generate_regular_inst_plan`)
    (GEN_ALL (SRULE [asm_sym_rel_core_own]
      (Q.INST [`code_ok` |->
        `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
        (SPEC_ALL (MP sym_rf_copy_preparation_execution_mode_conditional
          sym_rf_replay_interfaces))))) >>
  disch_then (drule_at (Pat `asm_sym_rel_own`)) >>
  simp[] >> disch_then irule >>
  rpt gen_tac >> strip_tac >> metis_tac[asm_sym_steps_mode_sim]
QED

Theorem sym_revert_forward_frame_sim_deep_own:
  !allow_own own lo prog env fuel ctx cp o2pc liveness dfg cfg fn bb i j base ps vs ast ops
   ps_end ra rest mem0 ret srest labs0 ss.
    code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ generated_plan_state_wf_marked base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps ast ss ==>
    !a vs_end. exec_block fuel ctx bb vs = Abort a vs_end ==>
    ?n ast_end.
      ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
       (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
      venom_asm_terminal_rel vs_end ast_end /\
      sym_terminal (sym_steps_mode allow_own prog env own n ss)
Proof
  rpt gen_tac >> strip_tac >> gvs[sym_frame_inv_own_def] >>
  drule sym_rf_copy_preparation_interface_own >> simp[] >> disch_then (mk_asm "copy") >>
  drule sym_terminal_transfer_own >> simp[] >> disch_tac >>
  qx_gen_tac `a` >> qx_gen_tac `vs_end` >> strip_tac >>
  drule_at (Pat `generated_plan_state_wf_marked`) (GEN_ALL own_rf_kernel) >>
  disch_then (drule_at (Pat `fn_frame_inv`)) >>
  disch_then (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `asm_sym_rel_own`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok`)) >>
  simp[] >>
  disch_then (qspecl_then [`allow_own`, `fuel`, `j`, `labs0`, `a`, `vs_end`] mp_tac) >>
  simp[] >> disch_then irule >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (asm "copy" (qspecl_then [`own`, `env`, `allow_own`] MATCH_ACCEPT_TAC)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all asm_sym_steps_mode_sim >> simp[]) >>
  asm_rewrite_tac[]
QED
