(* Terminal memory-safe custom-error exit boundaries. *)
Theory stmtSimCustomErrorExit
Ancestors
  fragGasPathMem fragExecMem fragExec memSafeRun instMemFrontier gasCount
  abiEncoderRegisteredEffect venomExecSemantics venomInst venomState
  emitHelper compileEnv words arithmetic

Theorem custom_error_terminal_revert_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id REVERT [dst;len] []) /\
  eval_operand dst s = SOME (n2w d) /\
  eval_operand len s = SOME (n2w n) /\
  d+n <= s.vs_alloca_next /\ ~s.vs_halted ==>
  ?t. gas_path_mem ctx fn s 0 (Abort Revert_abort t) /\
    run_from 0 ctx fn s = Abort Revert_abort t /\
    mem_safe_run 0 ctx fn s /\
    abi_encoder_registered_effect ids [] s t
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id REVERT [dst;len] []) s =
    Abort Revert_abort (revert_state (set_returndata
      (TAKE (w2n (n2w n : bytes32))
        (DROP (w2n (n2w d : bytes32)) s.vs_memory ++
         REPLICATE (w2n (n2w n : bytes32)) 0w)) s))` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def] >>
  `inst_mem_below_frontier (mk_inst id REVERT [dst;len] []) s` by
    (simp[below_frontier_REVERT] >>
     `w2n (n2w d : bytes32) <= d /\ w2n (n2w n : bytes32) <= n` by
       simp[w2n_n2w, MOD_LESS_EQ] >>
     gvs[w2n_n2w] >> decide_tac) >>
  `mem_safe_step 0 ctx (mk_inst id REVERT [dst;len] []) s` by
    simp[mem_safe_step_non_invoke, mk_inst_def] >>
  qmatch_asmsub_abbrev_tac `step_inst 0 ctx _ s = Abort Revert_abort t` >>
  `gas_path_mem_edge ctx fn s 0 (Abort Revert_abort t)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[gas_count_step_def, mk_inst_def, exit_result_def] >> metis_tac[]) >>
  drule run_from_step_exit >> disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  conj_tac >- metis_tac[gas_path_mem_rules, exit_result_def] >>
  simp[Abbr `t`, abi_encoder_registered_effect_def, revert_state_def, set_returndata_def]
QED

Theorem custom_error_emit_revert_mem:
  emit_inst REVERT [dst;len] [] st = (x,en) /\
  fn_has_code st en fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  eval_operand len s = SOME (n2w n) /\ d+n <= s.vs_alloca_next ==>
  ?t. gas_path_mem ctx fn s 0 (Abort Revert_abort t) /\
    run_from 0 ctx fn s = Abort Revert_abort t /\
    mem_safe_run 0 ctx fn s /\
    abi_encoder_registered_effect ids [] s t
Proof
  strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  metis_tac[custom_error_terminal_revert_mem]
QED
