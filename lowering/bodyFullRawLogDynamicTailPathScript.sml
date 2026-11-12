(* Horizon-uniform concrete dynamic RawLog tail. *)
Theory bodyFullRawLogDynamicTailPath
Ancestors
  bodyFullRawLogDynamicPrepare bodyFullRawLogDynamicLog bodyFullRawLogDynamicData
  exprSimHashBoundary fragGasSeqPtr bodyFullGhostFrame
  exprLoweringProps loweringPosts bodyPtrDefs
  words list rich_list finite_map arithmetic emitHelper compileEnv exprLowering
  venomState venomExecSemantics exprSimProps loweringStateRelDefs

Theorem raw_log_dynamic_prepare_endpoints:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm s2) s G1 tn1 /\
  inst_seq_ptr D' lo ctx func PG G tn (emitted_insts sm s2) s G2 tn2 ==>
  G1 = G2 /\ tn1 = tn2
Proof
  strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  fs[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND]) >>
  fs[inst_seq_ptr_def] >>
  Cases_on `step_inst_base
    (mk_inst sm.cs_next_id MLOAD [data_op] [STRING #"%" (toString sm.cs_next_var)]) s` >> gvs[] >>
  rename1 `step_inst_base _ s = OK v` >>
  Cases_on `step_inst_base
    (mk_inst (sm.cs_next_id+1) ADD [data_op;Lit 32w]
      [STRING #"%" (toString (sm.cs_next_var+1))])
    (v with vs_inst_idx := SUC s.vs_inst_idx)` >> gvs[]
QED

Theorem raw_log_dynamic_tail_path:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~ctx_has_dalloca ctx /\ LENGTH ops < dimword (:256) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (data_op::ops) /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_type (Call ann RawLog es_call dflt) = NoneT /\
  post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
  expr_has_effect (Call ann RawLog es_call dflt) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
    expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
    ptr_buf_ok cenv data data_op G s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    eval_operands ops s = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn op = {}) ops /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
  ?t u G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G1,tn1) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    ghost_kept_at lo cenv ee sm G tn s G1 tn1 /\
    u = (t with <|vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
                  vs_inst_idx := LENGTH sb.cs_current_insts|>) /\
    stmt_state_rel H ctx func cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) u /\
    storage_well_formed_on cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G1 tn1 u
Proof
  strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- (pop_assum (qx_choose_then `H0` assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
        (qspec_then `H0` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      drule_all hash_dynamic_post_view >> strip_tac >>
      `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
        SOME (BaseTV (BytesT (Dynamic cap)))` by metis_tac[] >>
      `ptr_val_ok cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data_op G tn s /\
       expr_store_bound cx (BaseT (BytesT (Dynamic cap))) (BytesV bs) data_op s` by metis_tac[] >>
      `(?x. data_op = Var x /\ ptr_covers G tn x s (32+32*word_size (LENGTH bs))) /\
       b+32+LENGTH bs <= s.vs_alloca_next /\
       (!i. b<=i /\ i<b+32+LENGTH bs ==> i NOTIN tn.t_mem)` by
        (drule_all raw_log_dynamic_data_window >> simp[wordsTheory.w2n_n2w, LESS_MOD] >>
         `b < dimword (:256)` by decide_tac >> simp[LESS_MOD]) >>
      mp_tac (Q.INST [`D` |-> `DF (H0 : (bool # 256 word # type_value) list # num list)`,
        `topics` |-> `MAP event_value_to_word vals`]
        (INST_TYPE [alpha |-> ``:word8``] raw_log_dynamic_prepare_joint)) >>
      (impl_tac >- (simp[LESS_MOD] >> metis_tac[ADD_COMM, ADD_ASSOC])) >> strip_tac >>
      qexistsl [`t`,
        `t with <|vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
                  vs_inst_idx := LENGTH sb.cs_current_insts|>`, `G1`, `tn1`] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
        (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      mp_tac (Q.INST [`D` |-> `DF (H : (bool # 256 word # type_value) list # num list)`,
        `topics` |-> `MAP event_value_to_word vals`]
        (INST_TYPE [alpha |-> ``:word8``] raw_log_dynamic_prepare_joint)) >>
      (impl_tac >- (simp[LESS_MOD] >> metis_tac[ADD_COMM, ADD_ASSOC])) >> strip_tac >>
      `t' = t` by gvs[] >>
      `G1' = G1 /\ tn1' = tn1` by metis_tac[raw_log_dynamic_prepare_endpoints] >>
      gvs[] >>
      `expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) (Var x) s` by metis_tac[] >>
      `stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H)` by fs[expr_post_def] >>
      `t = s with vs_vars := t.vs_vars` by
        (qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
      `stmt_state_rel H ctx func cenv cx ee t` by
        (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
         irule stmt_state_rel_vars_frame >> simp[] >>
         fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      `t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next` by
        (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
      `b+32+LENGTH bs <= t.vs_alloca_next /\
       (!j. b+32 <= j /\ j < b+32+LENGTH bs ==> j NOTIN tn1.t_mem) /\
       mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
       EVERY (\op. op_taint tn1 op = {}) (ptr_op::len_op::ops) /\
       (LENGTH bs <> 0 ==> ?x. ptr_op = Var x /\ ptr_covers G1 tn1 x t (LENGTH bs))` by
        (simp[] >> metis_tac[ADD_ASSOC, ADD_COMM]) >>
      drule_all raw_log_dynamic_log_joint >>
      disch_then (qspec_then `s2.cs_next_id` mp_tac) >>
      disch_then (qspec_then `PG` mp_tac) >>
      simp[LET_THM] >> strip_tac >> FAIL_TAC "path join") >>
  gvs[]
QED
