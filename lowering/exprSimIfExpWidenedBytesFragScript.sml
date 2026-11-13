Theory exprSimIfExpWidenedBytesFrag
Ancestors
  exprSimIfExpWidenedBytes fragExec exprSimProps exprSimBufferStore
  context emitHelper compileEnv freshWrites venomInst exprSimDefs stmtSimDefs
  rich_list exprLoweringProps loweringHalt venomState

Theorem bytestring_store_allocated_frag_frame:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  is_bytestring_type aty /\ evaluate_type (get_tenv cx) aty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v (w2n w) s.vs_memory /\
  type_memory_size tv < dimword (:256) /\ type_memory_size tv <= N /\
  FLOOKUP s.vs_allocas aid = SOME (w2n d,N) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= w2n d \/ w2n d+N <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n d) N) /\
  (!q. val_in_memory tv v (w2n d) q.vs_memory /\
    stmt_state_rel ctx func ce cx es q /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+N <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==> Q q) ==>
  frag_exec ctx sa sb (\z. z = s) Q R
Proof
  strip_tac >>
  drule_all bytestring_store_allocated_frame >> strip_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by (qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
      simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def,
        emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[] >> simp[emitted_insts_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, IS_PREFIX_APPEND] >>
  first_x_assum irule >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `(q with <|vs_memory := _; vs_vars := _|>) = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >>
  simp[]
QED
