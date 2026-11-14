(* Terminal memory-safe custom-error exit boundaries. *)
Theory stmtSimCustomErrorExit
Ancestors
  fragGasPathMem fragExecMem fragExec memSafeRun instMemFrontier gasCount
  abiEncoderRegisteredEffect venomExecSemantics venomInst venomState
  emitHelper compileEnv words arithmetic
  bodyFieldMemoryProps abiEncoderWindowSequence

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

Theorem custom_error_add_run:
  emit_op ADD [lhs;rhs] st = (out,en) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  fn_has_code st en fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (OK t) /\
    eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    t.vs_alloca_next = s.vs_alloca_next /\
    (!op. (!x. op = Var x ==> not_fresh_at st x) ==>
      eval_operand op t = eval_operand op s) /\
    abi_encoder_registered_effect ids [] s t
Proof
  strip_tac >> drule_all window_emit_add_pure >> strip_tac >>
  `run_inst_seq (emitted_insts st en) s = OK t` by
    metis_tac[window_pure_seq_def, window_seq_def] >>
  drule_all attr_add_gas_path >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    metis_tac[window_pure_seq_def, window_seq_labels] >>
  qexists_tac `t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  simp_tac (srw_ss()) [] >>
  `en.cs_current_bb = st.cs_current_bb` by
    metis_tac[window_pure_seq_def, window_seq_def] >>
  `abi_encoder_registered_effect ids [] s t` by
    metis_tac[window_pure_seq_registered_effect] >>
  gvs[window_pure_seq_def] >>
  conj_tac >- (rpt strip_tac >> Cases_on `op` >>
    gvs[eval_operand_def, window_seq_def]) >>
  gvs[abi_encoder_registered_effect_def]
QED

Theorem custom_error_revert_suffix_run:
  emit_op ADD [buf; Lit 28w] st = (offset,sn) /\
  (if no_args then len = Lit 4w /\ sr = sn
   else emit_op ADD [Lit 4w;encoded_len] sn = (len,sr)) /\
  emit_inst REVERT [offset;len] [] sr = (x,en) /\
  fn_has_code st sn fn /\ fn_has_code sn sr fn /\ fn_has_code sr en fn /\
  eval_operand buf s = SOME (n2w d) /\
  (~no_args ==> eval_operand encoded_len s = SOME (n2w k) /\
    (!v. encoded_len = Var v ==> not_fresh_at st v)) /\
  d+B+32 <= s.vs_alloca_next /\ d+B+32 < dimword (:256) /\ k <= B /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx fn s 0 (Abort Revert_abort t) /\
    (?fuel. run_from fuel ctx fn s = Abort Revert_abort t /\
      mem_safe_run fuel ctx fn s) /\
    abi_encoder_registered_effect ids [] s t
Proof
  strip_tac >>
  `eval_operand (Lit 28w) s = SOME 28w` by simp[eval_operand_def] >>
  drule_all custom_error_add_run >>
  disch_then (qspecl_then [`ids`,`ctx`] strip_assume_tac) >>
  rename1 `gas_path_mem ctx fn s 0 (OK u)` >>
  `eval_operand offset u = SOME (n2w (d+28))` by
    simp[word_add_n2w] >>
  Cases_on `no_args`
  >- (gvs[] >>
      `eval_operand (Lit 4w) u = SOME (n2w 4)` by simp[eval_operand_def] >>
      `d+28+4 <= u.vs_alloca_next` by decide_tac >>
      `?t. gas_path_mem ctx fn u 0 (Abort Revert_abort t) /\
        abi_encoder_registered_effect ids [] u t` by
        metis_tac[custom_error_emit_revert_mem] >>
      `gas_path_mem ctx fn s 0 (Abort Revert_abort t)` by
        metis_tac[gas_path_mem_then, ADD_0] >>
      qexists_tac `t` >>
      metis_tac[gas_path_mem_exec, exit_result_def,
        abi_encoder_registered_effect_trans]) >>
  gvs[] >>
  `eval_operand encoded_len u = SOME (n2w k)` by metis_tac[] >>
  `eval_operand (Lit 4w) u = SOME 4w` by simp[eval_operand_def] >>
  drule_all custom_error_add_run >>
  disch_then (qspecl_then [`ids`,`ctx`] strip_assume_tac) >>
  rename1 `gas_path_mem ctx fn u 0 (OK v)` >>
  `eval_operand offset v = SOME (n2w (d+28))` by metis_tac[] >>
  `eval_operand len v = SOME (n2w (4+k))` by
    (qpat_x_assum `eval_operand len v = _` mp_tac >>
     simp_tac (srw_ss()) [word_add_n2w]) >>
  `d+28+(4+k) <= v.vs_alloca_next` by decide_tac >>
  `?t. gas_path_mem ctx fn v 0 (Abort Revert_abort t) /\
    abi_encoder_registered_effect ids [] v t` by
    metis_tac[custom_error_emit_revert_mem] >>
  `gas_path_mem ctx fn s 0 (Abort Revert_abort t)` by
    metis_tac[gas_path_mem_then, ADD_0] >>
  `abi_encoder_registered_effect ids [] s t` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  qexists_tac `t` >>
  metis_tac[gas_path_mem_exec, exit_result_def]
QED
