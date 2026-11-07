(* Allocation-map extension across successful non-INVOKE sequences. *)
Theory stmtSimLogSuffixFrame
Ancestors
  stmtSimLogSuffix stmtSimLogSuffixCode venomMemProofs venomExecSemantics
  venomState venomInst finite_map list exprLoweringProps

Theorem log_step_old_allocas[local]:
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t ==>
  !aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[update_var_def, FLOOKUP_UPDATE] >>
      Cases_on `inst.inst_id = aid` >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_allocas] >> simp[]
QED

Theorem log_run_old_allocas:
  !code s t. run_inst_seq code s = OK t /\
    EVERY (\i. i.inst_opcode <> INVOKE) code ==>
    !aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >>
  rename1 `step_inst_base head s = OK middle` >>
  `FLOOKUP middle.vs_allocas aid = SOME b` by
    metis_tac[log_step_old_allocas] >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_success_suffix_framed_run:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fresh_vars_wrt limit_st s /\ sb.cs_next_var <= limit_st.cs_next_var /\
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
    fresh_vars_wrt limit_st t /\ inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!aid a k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >>
  `EVERY (supported_scalar_type o SND) xs` by
    (gvs[EVERY_MAP, LIST_REL_EL_EQN, EVERY_EL, combinTheory.o_DEF] >>
     metis_tac[LIST_REL_LENGTH]) >>
  drule_all log_success_suffix_code >> strip_tac >>
  drule_all log_success_suffix_run >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[Excl "enc_def"] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> irule log_run_old_allocas >>
  qexists_tac `emitted_insts sm sb` >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[]
QED
