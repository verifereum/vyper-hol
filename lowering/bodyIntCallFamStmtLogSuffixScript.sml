(* Seam 2 joint induction, a frozen helper leaf for the Log statement leaf:
   the Log suffix (topic hashing, data store, ABI encode, LOG) run from sm,
   as stmtSimLogSuffixFrameTheory.log_success_suffix_framed_run concludes
   but with no fresh_vars_wrt premise (the suffix's fresh variables may
   already be bound, e.g. on a later loop iteration, and are overwritten),
   and with a memory and allocation frame: every byte outside the suffix's
   own allocations is unchanged (an ALLOCA executed before returns its old
   region, so the frame is by allocation id, not by the frontier), the
   allocations stay above lo, and the frontier does not move down. *)
Theory bodyIntCallFamStmtLogSuffix
Ancestors
  bodyIntCallJointContract stmtSimLogSuffixFrame stmtSimLogSuffixActual

Theorem intcall_log_suffix_run:
  !ce id h tys flags args sa xs sm ops st lctx ty sb ctx func cx es s vs
   topics avs lo.
    ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
    compile_log_eval_all ce args sa = (xs,sm) /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
    stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
    allocas_above lo s /\
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
      (!a k. (!aid b z. sm.cs_next_id <= aid /\ aid < sb.cs_next_id /\
                FLOOKUP t.vs_allocas aid = SOME (b,z) ==> a + k <= b \/ b + z <= a) ==>
             mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
      allocas_above lo t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  cheat
QED
