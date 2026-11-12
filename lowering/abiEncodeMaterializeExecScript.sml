Theory abiEncodeMaterializeExec
Ancestors
  exprSimAlloc valueCopy context compileEnv exprLowering exprLoweringProps
  freshWrites venomState venomInst finite_map

(* Allocation boundary: code membership is discharged from the compilation
   interval rather than exposed to materialization's semantic consumer. *)
Theorem materialize_alloc_run:
  !ctx func ce cx es sa sm buf ty s.
    compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
    fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    type_memory_bytes ce ty < dimword (:256) ==>
    ?u w. run_inst_seq (emitted_insts sa sm) s = OK u /\
      stmt_state_rel ctx func ce cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_bytes ce ty) /\
      w2n w + type_memory_bytes ce ty < dimword (:256) /\
      u.vs_memory = s.vs_memory /\ sa.cs_next_id < sm.cs_next_id /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) (type_memory_bytes ce ty) b len) /\
      (!name b len. local_region ce es.scopes u name b len ==>
         regions_disjoint (w2n w) (type_memory_bytes ce ty) b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at sm p)
Proof
  rpt strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> simp[]
QED

(* The store starts after unwrap, which may itself have allocated.  Its
   starting allocation witness and destination variable are retained; no
   equality between the pre-unwrap and post-unwrap memories is required. *)
Theorem materialize_store_owned_run:
  !ce src p ty sa sb s tenv tv v sw dw aid.
    compile_store_memory ce src (Var p) ty ty sa = ((),sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce ty = type_memory_size tv /\
    (if is_word_type ty then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory) /\
    type_memory_size tv + 64 < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      lookup_var p t = SOME dw /\
      FLOOKUP t.vs_allocas aid = SOME (w2n dw,type_memory_size tv) /\
      t.vs_allocas = s.vs_allocas /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!off len. off + len <= w2n dw \/ w2n dw + type_memory_size tv <= off ==>
        mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt strip_tac >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s`
      (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
