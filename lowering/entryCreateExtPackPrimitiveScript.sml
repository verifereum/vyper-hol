(* Scopes for the straight-line primitives of external request packing. *)
Theory entryCreateExtPackPrimitive
Ancestors
  entryCreatePathScope bodyFullExtCallSelectorReady abiBuiltinAllocation
  emitHelperProps fragExec venomExecSemantics venomState venomInst venomInstProps gasEvents
  createSizePrefixReplay createMarkedPath fragGasOrigin relation list arithmetic
  entryCreateFocusSpec entryCreateCompletedCut abiEncoderProps exprLoweringProps pred_set

(* Keep the cursor update on the concrete successor of the installed step.
   The enclosing band may also include further packing instructions. *)
Theorem extcall_pack_step[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_id IN frag_ids a b /\ s.vs_inst_idx < LENGTH b.cs_current_insts /\
  ~s.vs_halted /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK u ==>
  create_expr_prefix a b explicit ctx fn s []
    (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def,create_prefix_step_def] >>
  simp[gas_origin_edge_def] >> qexists_tac `0` >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  simp[gas_events_step_def]
QED

Theorem extcall_pack_single[local]:
  fn_has_code x y fn /\
  y.cs_current_bb = x.cs_current_bb /\
  y.cs_current_insts = x.cs_current_insts ++ [i] /\
  i.inst_id = x.cs_next_id /\
  a.cs_next_id <= x.cs_next_id /\ x.cs_next_id < b.cs_next_id /\
  LENGTH y.cs_current_insts <= LENGTH b.cs_current_insts /\
  ~s.vs_halted /\ s.vs_current_bb = x.cs_current_bb /\
  s.vs_inst_idx = LENGTH x.cs_current_insts /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK u ==>
  create_expr_prefix a b explicit ctx fn s []
    (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  create_operand_at y (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  ~u.vs_halted
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i` by
    (drule_all fn_has_code_same_block >> simp[] >> metis_tac[]) >>
  `SUC s.vs_inst_idx = LENGTH y.cs_current_insts` by simp[] >>
  `i.inst_id IN frag_ids a b` by simp[frag_ids_def] >>
  `s.vs_inst_idx < LENGTH b.cs_current_insts` by decide_tac >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    metis_tac[step_preserves_control_flow,step_preserves_halted] >>
  drule_all extcall_pack_step >> simp[create_operand_at_def]
QED

Theorem extcall_pack_add_prefix[local]:
  emit_op ADD args x = (op,y) /\ fn_has_code x y fn /\
  a.cs_next_id <= x.cs_next_id /\ x.cs_next_id < b.cs_next_id /\
  LENGTH y.cs_current_insts <= LENGTH b.cs_current_insts /\
  ~s.vs_halted /\ create_operand_at x s /\
  run_inst_seq (emitted_insts x y) s = OK u ==>
  create_expr_prefix a b explicit ctx fn s []
    (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  create_operand_at y (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  ~u.vs_halted
Proof
  strip_tac >> drule emit_op_same_blocks >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  irule extcall_pack_single >> simp[] >>
  qexists_tac `x` >>
  fs[mk_inst_def,is_terminator_def,same_blocks_def,create_operand_at_def,
     run_inst_seq_def,AllCaseEqs()]
QED

Theorem extcall_pack_add_scope:
  emit_op ADD args a = (op,b) /\ fn_has_code a b fn /\
  ~s.vs_halted /\ create_operand_at a s /\
  run_inst_seq (emitted_insts a b) s = OK u ==>
  create_operand_full_scope a b explicit ctx fn s []
    (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  strip_tac >>
  `a.cs_next_id < b.cs_next_id` by (drule emitted_insts_emit_op >> simp[]) >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`a` |-> `x`,`b` |-> `y`]
    extcall_pack_add_prefix)) >>
  simp[create_operand_full_scope_def,GSYM create_operand_at_def]
QED

Theorem extcall_pack_alloc_prefix[local]:
  compile_alloc_buffer n x = (buf,y) /\ fn_has_code x y fn /\
  a.cs_next_id <= x.cs_next_id /\ x.cs_next_id < b.cs_next_id /\
  LENGTH y.cs_current_insts <= LENGTH b.cs_current_insts /\
  ~s.vs_halted /\ create_operand_at x s /\
  run_inst_seq (emitted_insts x y) s = OK u ==>
  create_expr_prefix a b explicit ctx fn s []
    (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  create_operand_at y (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  ~u.vs_halted
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  irule extcall_pack_single >> simp[] >> qexists_tac `x` >>
  fs[mk_inst_def,is_terminator_def,same_blocks_def,create_operand_at_def,
     run_inst_seq_def,AllCaseEqs()]
QED

Theorem extcall_pack_store_prefix[local]:
  emit_void MSTORE args x = ((),y) /\ fn_has_code x y fn /\
  a.cs_next_id <= x.cs_next_id /\ x.cs_next_id < b.cs_next_id /\
  LENGTH y.cs_current_insts <= LENGTH b.cs_current_insts /\
  ~s.vs_halted /\ create_operand_at x s /\
  run_inst_seq (emitted_insts x y) s = OK u ==>
  create_expr_prefix a b explicit ctx fn s []
    (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  create_operand_at y (u with vs_inst_idx := LENGTH y.cs_current_insts) /\
  ~u.vs_halted
Proof
  strip_tac >> drule emit_void_same_blocks >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  irule extcall_pack_single >> simp[] >> qexists_tac `x` >>
  fs[mk_inst_def,is_terminator_def,same_blocks_def,create_operand_at_def,
     run_inst_seq_def,AllCaseEqs()]
QED

Theorem extcall_pack_buffer_prefix[local]:
  compile_alloc_buffer n a = (buf,m) /\ emit_void MSTORE args m = ((),c) /\
  fn_has_code a m fn /\ fn_has_code m c fn /\
  c.cs_next_id <= b.cs_next_id /\ LENGTH c.cs_current_insts <= LENGTH b.cs_current_insts /\
  ~s.vs_halted /\ create_operand_at a s /\
  run_inst_seq (emitted_insts a m) s = OK u /\
  run_inst_seq (emitted_insts m c) (u with vs_inst_idx := LENGTH m.cs_current_insts) = OK v ==>
  create_expr_prefix a b explicit ctx fn s []
    (v with vs_inst_idx := LENGTH c.cs_current_insts) /\
  create_operand_at c (v with vs_inst_idx := LENGTH c.cs_current_insts) /\
  ~v.vs_halted
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `a.cs_next_id < b.cs_next_id /\ a.cs_next_id <= m.cs_next_id /\
   m.cs_next_id < b.cs_next_id /\ LENGTH m.cs_current_insts <= LENGTH b.cs_current_insts` by
    (fs[] >> decide_tac) >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`a` |-> `x`] extcall_pack_alloc_prefix)) >>
  disch_then (qspecl_then [`explicit`,`ctx`] strip_assume_tac) >>
  `~(u with vs_inst_idx := LENGTH m.cs_current_insts).vs_halted` by simp[] >>
  drule_all extcall_pack_store_prefix >>
  disch_then (qspecl_then [`explicit`,`ctx`] strip_assume_tac) >>
  conj_tac >-
    (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
       create_expr_prefix_append)) >>
     qexists_tac `u with vs_inst_idx := LENGTH m.cs_current_insts` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem extcall_pack_buffer_scope:
  compile_alloc_buffer n a = (buf,m) /\ emit_void MSTORE args m = ((),b) /\
  fn_has_code a m fn /\ fn_has_code m b fn /\
  ~s.vs_halted /\ create_operand_at a s /\
  run_inst_seq (emitted_insts a m) s = OK u /\
  run_inst_seq (emitted_insts m b) (u with vs_inst_idx := LENGTH m.cs_current_insts) = OK v ==>
  create_operand_full_scope a b explicit ctx fn s []
    (OK (v with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`b` |-> `c`] extcall_pack_buffer_prefix)) >>
  simp[create_operand_full_scope_def,GSYM create_operand_at_def]
QED

Theorem extcall_selector_run_scope[local]:
  compile_alloc_buffer n a = (buf,m) /\ emit_void MSTORE args m = ((),c) /\
  emit_op ADD add_args c = (off,b) /\
  fn_has_code a m fn /\ fn_has_code m c fn /\ fn_has_code c b fn /\
  ~s.vs_halted /\ create_operand_at a s /\
  extcall_pack_raw a m s u /\ extcall_pack_raw m c u v /\ extcall_pack_raw c b v t ==>
  create_operand_full_scope a b explicit ctx fn s [] (OK t)
Proof
  rewrite_tac[extcall_pack_raw_def] >> strip_tac >>
  qpat_x_assum `u = _ with vs_inst_idx := _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _ with vs_inst_idx := _` SUBST_ALL_TAC >>
  qpat_x_assum `t = _ with vs_inst_idx := _` SUBST_ALL_TAC >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  qpat_assum `emit_op ALLOCA _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `c.cs_next_id <= b.cs_next_id /\ a.cs_next_id <= c.cs_next_id /\
   c.cs_next_id < b.cs_next_id /\ LENGTH c.cs_current_insts <= LENGTH b.cs_current_insts` by
    (fs[] >> decide_tac) >>
  drule_all extcall_pack_buffer_prefix >>
  disch_then (qspecl_then [`explicit`,`ctx`] strip_assume_tac) >>
  rename1 `create_operand_at c (raw_store with vs_inst_idx := _)` >>
  `~(raw_store with vs_inst_idx := LENGTH c.cs_current_insts).vs_halted` by simp[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`b` |-> `y`] extcall_pack_add_prefix)) >>
  disch_then (qspecl_then [`explicit`,`ctx`] strip_assume_tac) >>
  pure_rewrite_tac[create_operand_full_scope_def,exec_result_case_def] >> BETA_TAC >>
  conj_tac >-
    (irule (SIMP_RULE (srw_ss()) [] (Q.INST [`left` |-> `[]`,`right` |-> `[]`]
       create_expr_prefix_append)) >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  fs[create_operand_at_def]
QED

(* Apply this to extcall_selector_packing_ready_with_raw_endpoints with its
   ready, memory, gas, and ghost post as P. Scope and P use the same tuple. *)
Theorem extcall_selector_ready_scoped:
  compile_alloc_buffer n a = (buf,m) /\ emit_void MSTORE args m = ((),c) /\
  emit_op ADD add_args c = (off,b) /\
  fn_has_code a m fn /\ fn_has_code m c fn /\ fn_has_code c b fn /\
  ~s.vs_halted /\ create_operand_at a s /\
  (?calldata t Gf tf.
    (?u v. extcall_pack_raw a m s u /\ extcall_pack_raw m c u v /\
           extcall_pack_raw c b v t) /\ P calldata t Gf tf) ==>
  ?calldata t Gf tf.
    create_operand_full_scope a b explicit ctx fn s [] (OK t) /\ P calldata t Gf tf
Proof
  strip_tac >> qexistsl_tac [`calldata`,`t`,`Gf`,`tf`] >> simp[] >>
  drule_all extcall_selector_run_scope >> simp[]
QED
