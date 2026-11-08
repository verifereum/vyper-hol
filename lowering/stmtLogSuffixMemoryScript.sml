(* The memory checks of the log statement's suffix: after the arguments,
   the topic hashes, the data buffer and its stores, the encode buffer and
   the tuple encoder, and LOG, as log_success_suffix_actual_run runs them.
   Every access lies in an argument's footprint (expr_val_at: an allocation
   or a local's region) or in one of the suffix's own two ALLOCA buffers,
   all below the allocation frontier; ALLOCA only raises the frontier.
   A bytestring argument is copied whole, its length word and its bytes
   rounded up to a multiple of 32 (compile_store_bytestring), which can
   read past val_footprint; the last premise puts that rounded range
   below the frontier. *)
Theory stmtLogSuffixMemory
Ancestors
  stmtSimLogSuffixActual stmtSimLogArgs stmtSimLogSource fragExecMem
  exprLoweringProps stmtLowering compileEnv loweringPosts
  vyperEvent vyperInterpreter vyperState venomState

Theorem log_success_suffix_mem_ok:
  ce.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags) /\
  log_eval_view ce args sa xs sm /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs /\
  LIST_REL (\arg v. !w n.
    ~is_word_type (SND arg) /\ eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n + 31) DIV 32) <= s.vs_alloca_next) xs vs ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s /\
  !t. run_inst_seq (emitted_insts sm sb) s = OK t ==>
      s.vs_alloca_next <= t.vs_alloca_next
Proof
  cheat
QED
