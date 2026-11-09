(* Apply the Log suffix to the actual endpoint, hiding its arbitrary limit. *)
Theory stmtSimLogSuffixActual
Ancestors
  stmtSimLogSuffixFrame compileEnv loweringStateRelDefs context venomState finite_map pred_set
  ASCIInumbers list

Theorem log_finite_name_bound[local]:
  !names. FINITE names ==>
    ?bound:num. !n. bound <= n ==> STRING #"%" (toString n) NOTIN names
Proof
  ho_match_mp_tac FINITE_INDUCT >> simp[] >> rpt strip_tac >>
  rename1 `STRING #"%" (toString _) <> name` >>
  Cases_on `?k:num. name = STRING #"%" (toString k)`
  >- (pop_assum strip_assume_tac >> qexists_tac `MAX bound (SUC k)` >>
      simp[ASCIInumbersTheory.toString_11] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  qexists_tac `bound` >> rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem log_fresh_limit_exists:
  !s sb. ?limit_st. sb.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st s
Proof
  rpt gen_tac >> qspec_then `FDOM s.vs_vars` mp_tac log_finite_name_bound >>
  simp[] >> strip_tac >>
  qexists_tac `sb with cs_next_var := MAX sb.cs_next_var bound` >>
  simp[fresh_vars_wrt_def, arithmeticTheory.GREATER_EQ] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

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
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  strip_tac >> qspecl_then [`s`, `sb`] strip_assume_tac log_fresh_limit_exists >>
  drule_all log_success_suffix_framed_run >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED
