(* Apply the Log suffix to the actual endpoint, hiding its arbitrary limit. *)
Theory stmtSimLogSuffixActual
Ancestors
  freshVarLimit stmtSimLogSuffixFrame compileEnv loweringStateRelDefs context venomState finite_map pred_set
  ASCIInumbers list

Theorem log_success_suffix_actual_run:
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
    (log_non_indexed_values flags vs) = SOME avs ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs) |>]) t /\
    inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid a k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> qspecl_then [`s`, `sb`] strip_assume_tac log_fresh_limit_exists >>
  drule_all log_success_suffix_framed_run >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC
QED
