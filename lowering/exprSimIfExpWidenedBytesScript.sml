(* Dynamic bytestring copies preserve frames outside an explicitly allocated
   destination, even when its capacity exceeds the encoded value's size. *)
Theory exprSimIfExpWidenedBytes
Ancestors
  exprSimBufferStore stmtSimLogEncodeFrame stmtSimLogExecFields
  context compileEnv emitHelper exprSimDefs stmtSimDefs valueEncodingTyping
  freshWrites venomInst list exprLoweringProps

Theorem bytestring_store_memory_mono[local]:
  compile_store_bytestring src dst sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK q ==>
  LENGTH s.vs_memory <= LENGTH q.vs_memory
Proof
  strip_tac >> irule log_encode_run_memory_mono >>
  qexists_tac `emitted_insts sa sb` >> simp[] >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, log_encode_safe_opcode_def, mk_inst_def]
QED

Theorem bytestring_store_allocated_frame:
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
    regions_disjoint off (type_memory_size itv) (w2n d) N) ==>
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
    val_in_memory tv v (w2n d) q.vs_memory /\
    stmt_state_rel ctx func ce cx es q /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d+N <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  drule_all buffer_typed_bytestring_header >> strip_tac >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  drule_all buffer_store_bytestring_encoding >> strip_tac >>
  drule_all bytestring_store_memory_mono >> strip_tac >>
  `!a k. a+k <= w2n d \/ w2n d+N <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `stmt_state_rel ctx func ce cx es q` by
    (irule buffer_store_state_frame >>
     qexistsl_tac [`w2n d`,`N`,`s`,`sa`] >> asm_rewrite_tac []) >>
  qexists_tac `q` >> asm_rewrite_tac []
QED
