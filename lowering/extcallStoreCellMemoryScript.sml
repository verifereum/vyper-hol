(* Literal stores used by external-call argument tuple construction. *)
Theory extcallStoreCellMemory
Ancestors
  bodyCopyMemory exprSimMemUnwrap exprSimBufferStore abiTupleProps
  stmtReasonMemory instMemFrontier fragExecMem fragGasPathMem
  exprLoweringProps emitHelperProps emitHelper compileEnv valueEncodingProps
  venomExecSemantics venomState venomInst words list

Theorem extcall_store_copy_mem:
  emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
  n < dimword (:256) /\
  (n = 0 \/ w2n w + n <= s.vs_alloca_next) /\
  (n = 0 \/ w2n d + n <= s.vs_alloca_next) /\
  val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    val_in_memory tv v (w2n d) t.vs_memory /\
    t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t /\
    (!a k. a + k <= w2n d \/ w2n d + n <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (mcopy (w2n d) (w2n w) n s)` by
    (asm_rewrite_tac [] >> irule run_inst_seq_sing_ok >>
     simp[step_mcopy_eq, eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY, eval_operand_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `val_in_memory tv v (w2n d) (mcopy (w2n d) (w2n w) n s).vs_memory` by
    (irule buffer_mcopy_encoding >> metis_tac[]) >>
  `!a k. a + k <= w2n d \/ w2n d + n <= a ==>
     mem_bytes_at a k (mcopy (w2n d) (w2n w) n s).vs_memory =
       mem_bytes_at a k s.vs_memory` by metis_tac[buffer_mcopy_exterior] >>
  qexists_tac `mcopy (w2n d) (w2n w) n s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  pure_rewrite_tac [venom_state_accfupds] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, REFL_TAC,
         simp[mcopy_def, write_memory_with_expansion_def]]
QED

Theorem extcall_store_word_mem:
  emit_void MSTORE [dst; src] sa = ((),sb) /\
  eval_operand dst s = SOME d /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\
  abi_tuple_word tv v /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    val_in_memory tv v (w2n d) t.vs_memory /\
    t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t /\
    (!a k. a + k <= w2n d \/ w2n d + 32 <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (mstore (w2n d) (typed_val_to_w256 tv v) s)` by
    (asm_rewrite_tac [] >> irule run_inst_seq_sing_ok >>
     simp[step_mstore_eq]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `val_in_memory tv v (w2n d)
      (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_memory` by
    metis_tac[abi_tuple_word_mstore] >>
  `!a k. a + k <= w2n d \/ w2n d + 32 <= a ==>
     mem_bytes_at a k (mstore (w2n d) (typed_val_to_w256 tv v) s).vs_memory =
       mem_bytes_at a k s.vs_memory` by metis_tac[mstore_mem_bytes_at_disjoint] >>
  qexists_tac `mstore (w2n d) (typed_val_to_w256 tv v) s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  pure_rewrite_tac [venom_state_accfupds] >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC, REFL_TAC,
         simp[mstore_def, write_memory_with_expansion_def]]
QED

Theorem extcall_store_bytestring_mem:
  compile_store_bytestring src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  mem_word_at (w2n w) s.vs_memory = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n w + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  val_in_memory tv v (w2n w) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size len /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    val_in_memory tv v (w2n d) t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\
    (!a k. a + k <= w2n d \/ w2n d + (32 + 32 * word_size len) <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  `mload (w2n w) s = n2w len` by metis_tac[mem_word_at_eq_mload] >>
  drule_all buffer_store_bytestring_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_store_bytestring_body_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     gvs[contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def,
       emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def]) >>
  drule_all straight_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `val_in_memory tv v (w2n d)
    (mcopy (w2n d) (w2n w) (32 + 32 * word_size len) s).vs_memory` by
    (irule buffer_mcopy_encoding >> metis_tac[]) >>
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  pure_rewrite_tac[venom_state_accfupds] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- (pure_rewrite_tac[lookup_var_def, venom_state_accfupds] >>
    asm_rewrite_tac[GSYM lookup_var_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm_rewrite_tac[] >> metis_tac[buffer_mcopy_exterior]
QED
