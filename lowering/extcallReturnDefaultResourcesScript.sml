(* Resource transport across the fresh-variable default-return control shell. *)
Theory extcallReturnDefaultResources
Ancestors
  extcallReturnDefaultRouting extcallReturnEntryBridge abiReturnPrefixTransport
  abiMalformedRecursiveInterface abiDecoderReentry exprLoweringProps
  exprSafeOperand compileEnv venomState finite_map list loweringPosts freshWrites emitHelper venomMemProps context rich_list venomExecSemantics venomInst

Theorem return_default_ready_transport:
  abi_return_decode_ready ctx func ce cx ee a sites dstid live base_op dst
    B cap bs d n s /\ a.cs_next_var <= b.cs_next_var /\
  stmt_state_rel ctx func ce cx ee t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  (!op w. abi_decoder_operand_live a.cs_next_var op /\
     eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  abi_return_decode_ready ctx func ce cx ee b sites dstid live base_op dst
    B cap bs d n t
Proof
  strip_tac >> fs[abi_return_decode_ready_def] >>
  `local_ptrs_reserved ce b` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand base_op t = SOME (n2w B) /\
   eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
  simp[abi_return_decode_ready_def] >> rpt conj_tac
  >- fs[abi_malformed_allocated_window_def]
  >- (fs[abi_malformed_destination_def] >> metis_tac[]) >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem return_default_shell_reserved:
  a.cs_next_var <= n1 /\ a.cs_next_var <= n2 /\
  u = jump_to lbl
    ((update_var (STRING #"%" (toString n2)) w2
      (update_var (STRING #"%" (toString n1)) w1 s))
      with vs_inst_idx := k) ==>
  (!x. not_fresh_at a x ==> lookup_var x u = lookup_var x s) /\
  (!op. abi_decoder_operand_live a.cs_next_var op ==>
     eval_operand op u = eval_operand op s) /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_returndata = s.vs_returndata /\ u.vs_halted = s.vs_halted
Proof
  strip_tac >> gvs[] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_asm1_tac
  >- (rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[]) >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
     not_fresh_at_def] >> metis_tac[]
QED

Theorem return_default_shell_state:
  a.cs_next_var <= n1 /\ a.cs_next_var <= n2 /\
  local_ptrs_reserved ce a /\ stmt_state_rel ctx func ce cx ee s /\
  u = jump_to lbl
    ((update_var (STRING #"%" (toString n2)) w2
      (update_var (STRING #"%" (toString n1)) w1 s))
      with vs_inst_idx := k) ==>
  stmt_state_rel ctx func ce cx ee u
Proof
  strip_tac >> gvs[] >>
  simp[stmt_state_rel_jump_to, stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_update_var >>
  conj_tac
  >- (irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]
QED

Theorem return_default_shell_wb_frame:
  a.cs_next_var <= n1 /\ a.cs_next_var <= n2 /\
  sa.cs_next_var <= a.cs_next_var /\ wb_frame ce es sa s0 s /\
  u = jump_to lbl
    ((update_var (STRING #"%" (toString n2)) w2
      (update_var (STRING #"%" (toString n1)) w1 s))
      with vs_inst_idx := k) ==>
  wb_frame ce es sa s0 u
Proof
  strip_tac >>
  `!x. not_fresh_at a x ==> lookup_var x u = lookup_var x s` by
    (drule_all return_default_shell_reserved >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    gvs[jump_to_def, update_var_def] >>
  fs[wb_frame_def, locals_kept_def] >> rpt conj_tac >>
  gvs[not_fresh_at_def]
QED

Theorem return_default_shell_ready:
  abi_return_decode_ready ctx func ce cx ee a sites dstid live base_op dst
    B cap bs d n s /\ a.cs_next_var <= b.cs_next_var /\
  a.cs_next_var <= n1 /\ a.cs_next_var <= n2 /\
  u = jump_to lbl
    ((update_var (STRING #"%" (toString n2)) w2
      (update_var (STRING #"%" (toString n1)) w1 s))
      with vs_inst_idx := k) ==>
  abi_return_decode_ready ctx func ce cx ee b sites dstid live base_op dst
    B cap bs d n u /\
  (!op. abi_decoder_operand_live a.cs_next_var op ==>
     eval_operand op u = eval_operand op s) /\
  (!op ty v. abi_decoder_operand_live a.cs_next_var op /\
     expr_val_rel cx ty v op s ==> expr_val_rel cx ty v op u) /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_returndata = s.vs_returndata /\ u.vs_halted = s.vs_halted
Proof
  strip_tac >> drule_all return_default_shell_reserved >> strip_tac >>
  `stmt_state_rel ctx func ce cx ee u` by
    (qpat_assum `abi_return_decode_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_return_decode_ready_def]) >>
     drule_all return_default_shell_state >> simp[]) >>
  conj_tac
  >- (drule_at (Pos hd) return_default_ready_transport >>
      disch_then irule >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> fs[expr_val_rel_def] >> gvs[]
QED

Theorem return_default_ready_entry:
  emit_op RETURNDATASIZE [] a = (rds,a1) /\
  emit_op ISZERO [rds] a1 = (test,a2) /\
  fresh_label "extcall_default" a2 = (dl,a3) /\
  fresh_label "extcall_decode" a3 = (cl,a4) /\
  fresh_label "extcall_exit" a4 = (xl,a5) /\
  emit_inst JNZ [test; Label dl; Label cl] [] a5 = ((),a6) /\
  fn_has_code a a2 func /\ fn_has_code a5 a6 func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) /\
  b.cs_current_bb = (if s.vs_returndata = [] then dl else cl) /\
  b.cs_current_insts = [] /\ a.cs_next_var <= b.cs_next_var /\
  abi_return_decode_ready ctx func ce cx ee a sites dstid live base_op dst
    B cap bs d n s /\ wb_frame ce es sa s0 s /\
  sa.cs_next_var <= a.cs_next_var ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    abi_return_decode_ready ctx func ce cx ee b sites dstid live base_op dst
      B cap bs d n u /\ wb_frame ce es sa s0 u /\
    (!op. abi_decoder_operand_live a.cs_next_var op ==>
       eval_operand op u = eval_operand op s) /\
    (!op ty v. abi_decoder_operand_live a.cs_next_var op /\
       expr_val_rel cx ty v op s ==> expr_val_rel cx ty v op u) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_returndata = s.vs_returndata /\ ~u.vs_halted /\
    u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >> drule_all return_default_shell_entry >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `a.cs_next_var <= a1.cs_next_var` by
    (qpat_x_assum `emit_op RETURNDATASIZE _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  qabbrev_tac `u = jump_to (if s.vs_returndata = [] then dl else cl) t` >>
  `u = jump_to (if s.vs_returndata = [] then dl else cl)
     ((update_var (STRING #"%" (toString a1.cs_next_var))
       (if s.vs_returndata = [] then 1w else 0w)
       (update_var (STRING #"%" (toString a.cs_next_var))
         (n2w (LENGTH s.vs_returndata)) s))
       with vs_inst_idx := LENGTH a2.cs_current_insts)` by simp[Abbr `u`] >>
  `a.cs_next_var <= a.cs_next_var` by simp[] >>
  qpat_assum `a.cs_next_var <= b.cs_next_var`
    (mp_then (Pos (el 2)) mp_tac return_default_shell_ready) >>
  disch_then drule_all >> strip_tac >>
  `wb_frame ce es sa s0 u` by
    (drule_all return_default_shell_wb_frame >> simp[]) >>
  qexists_tac `u` >> simp[Abbr `u`, jump_to_def, update_var_def]
QED

Theorem return_default_allocation_frontier:
  compile_alloc_buffer n a = (buf,b) /\
  run_inst_seq (emitted_insts a b) s = OK r ==>
  s.vs_alloca_next <= r.vs_alloca_next
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >>
  gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[emitted_insts_def, DROP_APPEND, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, AllCaseEqs()] >>
  strip_tac >> drule exec_alloca_alloca_next_mono >> simp[]
QED
