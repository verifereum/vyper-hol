(* Horizon-uniform concrete dynamic RawLog tail. *)
Theory bodyFullRawLogDynamicTailPath
Ancestors
  logEmitStep
  bodyFullRawLogDynamicPrepare bodyFullRawLogDynamicLog bodyFullRawLogDynamicData
  exprSimHashBoundary fragGasSeqPtr bodyFullGhostFrame
  exprLoweringProps loweringPosts bodyPtrDefs
  bodyFullRawLogDynamicSequenceFrame bodyFullRawLogDynamicSequence
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

Theorem raw_log_dynamic_tail_path_run:
  ~cx.txn.is_static /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  LENGTH ops < dimword (:256) /\
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
    alloca_history func u /\ tn1.t_mem = tn.t_mem /\
    (u with <|vs_logs := t.vs_logs; vs_inst_idx := t.vs_inst_idx|>) = t /\
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
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G1 tn1 u /\
    run_inst_seq (emitted_insts sm sb) s =
      OK (t with vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs])
Proof
  strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- (pop_assum (qx_choose_then `H0` assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
        (qspec_then `H0` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
        (qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
         qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
           (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
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
      `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
        (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
         fs[ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
      drule_all raw_log_dynamic_log_joint >>
      disch_then (qspec_then `s2.cs_next_id` mp_tac) >>
      disch_then (qspec_then `PG` mp_tac) >>
      simp[LET_THM] >> strip_tac >>
      `tn1.t_mem = tn.t_mem` by
        (irule raw_log_dynamic_prepare_memory_taint >> metis_tac[]) >>
      `((t with <|vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
                 vs_inst_idx := LENGTH sb.cs_current_insts|>) with
         <|vs_logs := t.vs_logs; vs_inst_idx := t.vs_inst_idx|>) = t` by simp[] >>
      `alloca_history func
        (t with <|vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
                  vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
        (irule raw_log_dynamic_sequence_history >> simp[] >>
         rpt (goal_assum $ drule_at Any) >>
         qpat_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
      `ghost_inv_at (DF H) lo d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G1 tn1
        (t with <|vs_logs := t.vs_logs ++ [encode_raw_event_values cx.txn.target vals bs];
                  vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
        (qpat_x_assum `ghost_inv_at (DF H) _ _ _ _ (_ with logs := _) _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         Cases_on `d`
         >- (simp[ghost_inv_at_def, ptr_covers_def, return_buf_ptr_def,
                  stor_taint_ok_at_def, lookup_var_def, ptrDisciplineTheory.allocas_from_def] >> strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
         rename1 `SOME rb` >> PairCases_on `rb` >>
         simp[ghost_inv_at_def, ptr_covers_def, return_buf_ptr_def,
              stor_taint_ok_at_def, lookup_var_def, ptrDisciplineTheory.allocas_from_def] >> strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
      simp[stmt_state_rel_inst_idx] >>
      drule_all (SRULE [LET_THM] raw_log_dynamic_sequence_path_run) >>
      simp[LET_THM, venom_state_fupdfupds] >> strip_tac >>
      fs[venom_state_fupdfupds]) >>
  gvs[]
QED

Theorem raw_log_dynamic_tail_path:
  ~cx.txn.is_static /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  LENGTH ops < dimword (:256) /\
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
    alloca_history func u /\ tn1.t_mem = tn.t_mem /\
    (u with <|vs_logs := t.vs_logs; vs_inst_idx := t.vs_inst_idx|>) = t /\
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
  strip_tac >> drule_all raw_log_dynamic_tail_path_run >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `t` (qx_choose_then `u`
      (qx_choose_then `G1` (qx_choose_then `tn1` assume_tac))))) >>
  qexistsl [`t`, `u`, `G1`, `tn1`] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

(* The static LOG abort retains the concrete preparation and its pointer checks. *)
Theorem raw_log_dynamic_static_tail_witness:
  cx.txn.is_static /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  LENGTH ops < dimword (:256) /\
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
    run_inst_seq (emitted_insts sm s2) s = OK t /\
    gas_origin_edge T explicit ctx func
      (t with vs_inst_idx := LENGTH s2.cs_current_insts) [] (Abort ExHalt_abort u) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort u,G1,tn1)
Proof
  strip_tac >>
  Cases_on `?H. valid_horizon cx st0 H ee.storage_trace`
  >- (pop_assum (qx_choose_then `H0` assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
        (qspec_then `H0` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
        (qpat_assum `expr_post H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
         qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
           (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
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
      qexistsl [`t`, `halt_state (set_returndata [] (t with vs_inst_idx := LENGTH s2.cs_current_insts))`,
                `G1`, `tn1`] >>
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
      `stmt_state_rel H ctx func cenv cx ee s` by fs[expr_post_def] >>
      `t = s with vs_vars := t.vs_vars` by
        (qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
      qabbrev_tac `q = t with vs_inst_idx := LENGTH s2.cs_current_insts` >>
      qabbrev_tac `i = mk_inst s2.cs_next_id LOG
        (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) []` >>
      `q.vs_call_ctx.cc_static` by
        (simp[Abbr `q`] >>
         qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
         fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
      `step_inst_base i q = Abort ExHalt_abort (halt_state (set_returndata [] q))` by
        (irule log_emit_static_step >> simp[Abbr `i`, venomInstTheory.mk_inst_def, Abbr `q`,
           eval_operand_def, lookup_var_def, eval_operands_def] >>
         metis_tac[]) >>
      `inst_mem_below_frontier i q /\ inst_dload_in_section i q` by
        (simp[Abbr `i`, instMemFrontierTheory.below_frontier_LOG,
           memSafeRunTheory.inst_dload_in_section_def, venomInstTheory.mk_inst_def,
           Abbr `q`, wordsTheory.w2n_n2w, LESS_MOD] >>
         rpt strip_tac >> gvs[wordsTheory.w2n_n2w, LESS_MOD] >>
         qpat_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
      `access_ok 0 G1 func i q` by
        (qunabbrev_tac `i` >> irule rawLogPtrInstTheory.log_access_ok >>
         simp[Abbr `q`, wordsTheory.w2n_n2w, LESS_MOD] >>
         rpt strip_tac >> gvs[ptr_covers_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
      `access_ok lo G1 func i q` by
        (qpat_x_assum `access_ok 0 _ _ _ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[ptrDisciplineTheory.access_ok_def] >> first_x_assum irule >>
         simp[] >> metis_tac[LESS_EQ_TRANS, DECIDE ``0 <= n:num``]) >>
      `taint_ok func tn1 i q` by
        (qunabbrev_tac `i` >> irule rawLogPtrInstTheory.log_taint_ok >>
         simp[Abbr `q`, wordsTheory.w2n_n2w, LESS_MOD]) >>
      `i.inst_opcode = LOG` by simp[Abbr `i`, venomInstTheory.mk_inst_def] >>
      `unitTransformDefs$dalloca_no_wrap i q` by
        simp[memSafeRunTheory.dalloca_no_wrap_non_dalloca] >>
      `ptrDiscipline$allocas_from lo q` by
        (simp[Abbr `q`, ptrDisciplineTheory.allocas_from_def] >>
         qpat_x_assum `ghost_inv_at (DF H) _ _ _ _ _ _ _ _` mp_tac >>
         simp[ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def] >>
         metis_tac[]) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
        (simp[Abbr `q`] >>
         qpat_assum `t = s with vs_vars := _` SUBST1_TAC >>
         fs[ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
      `ptr_inst_ok (DF H) lo 0 ctx func G1 tn1 i q` by
        simp[ptrSafeRunTheory.ptr_inst_ok_def,
           venomExecSemanticsTheory.step_inst_non_invoke] >>
      `sb.cs_current_bb = sm.cs_current_bb /\
       sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm s2 ++ [i] /\
       LENGTH s2.cs_current_insts = LENGTH sm.cs_current_insts + LENGTH (emitted_insts sm s2) /\
       EVERY (\j. j.inst_opcode <> INVOKE /\ ~venomInst$is_terminator j.inst_opcode /\ j.inst_opcode <> GAS)
         (emitted_insts sm s2) /\
       EVERY (\j. j.inst_opcode <> DALLOCA) (emitted_insts sm s2)` by
        (gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
             comp_return_def, fresh_var_def, fresh_id_def, emit_def, Abbr `i`] >>
         simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
         pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
         simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
      `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
            isPREFIX sb.cs_current_insts bb.bb_instructions` by
        (gvs[fragExecTheory.fn_has_code_def] >> metis_tac[]) >>
      `isPREFIX (emitted_insts sm s2) (DROP s.vs_inst_idx bb.bb_instructions)` by
        (gvs[IS_PREFIX_APPEND] >>
         pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
      `EVERY (\j. j.inst_opcode <> INVOKE /\ ~venomInst$is_terminator j.inst_opcode)
         (emitted_insts sm s2) /\
       FILTER (\j. j.inst_opcode = GAS) (emitted_insts sm s2) = []` by
        (simp[FILTER_EQ_NIL] >> gvs[EVERY_MEM]) >>
      `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
      `(ctx_has_dalloca ctx ==>
         !pre j post v. emitted_insts sm s2 = pre ++ j::post /\
           run_inst_seq pre s = OK v ==> unitTransformDefs$dalloca_no_wrap j v)` by
        (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
         qpat_x_assum `EVERY (\j. j.inst_opcode <> DALLOCA) _` mp_tac >>
         simp[EVERY_APPEND]) >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,G1,tn1)` by
        (drule_all run_inst_seq_gas_origin_ptr_path >> simp[Abbr `q`]) >>
      `~q.vs_halted /\ q.vs_current_bb = sm.cs_current_bb` by
        (simp[Abbr `q`] >> qpat_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
      `lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb q.vs_inst_idx = SOME i` by
        (simp[Abbr `q`] >> gvs[IS_PREFIX_APPEND] >>
         simp[venomInstTheory.get_instruction_def, EL_APPEND2, EL_APPEND1]) >>
      `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (q,G1,tn1) []
         (Abort ExHalt_abort (halt_state (set_returndata [] q)),G1,tn1)` by
        (rewrite_tac[fragGasOriginPtrTheory.gas_origin_ptr_edge_def] >> conj_tac
         >- (rewrite_tac[fragGasOriginTheory.gas_origin_edge_def] >> simp[] >>
             qexists `0` >>
             simp[step_inst_non_invoke, gasEventsTheory.gas_events_step_def,
                  memSafeRunTheory.mem_safe_step_non_invoke, fragExecTheory.exit_result_def]) >>
         rewrite_tac[fragGasPathPtrTheory.gas_path_ptr_edge_def] >> simp[] >>
         qexists `0` >>
         simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def,
              ptrSafeRunTheory.ptr_safe_step_def, fragExecTheory.exit_result_def]) >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (q,G1,tn1) []
         (Abort ExHalt_abort (halt_state (set_returndata [] q)),G1,tn1)` by
        (irule (cj 3 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >>
         simp[fragExecTheory.exit_result_def]) >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
         (Abort ExHalt_abort (halt_state (set_returndata [] q)),G1,tn1)` by
        (qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK q,G1,tn1)`
           (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
         disch_then (qspecl_then [`q`,`G1`,`tn1`,`[]`] mp_tac) >> simp[]) >>
      fs[fragGasOriginPtrTheory.gas_origin_ptr_edge_def]) >>
  gvs[]
QED

Theorem raw_log_dynamic_static_tail_path:
  cx.txn.is_static /\
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  LENGTH ops < dimword (:256) /\
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
  ?u G1 tn1. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort ExHalt_abort u,G1,tn1)
Proof
  disch_then (mp_tac o MATCH_MP raw_log_dynamic_static_tail_witness) >>
  rpt strip_tac >> qexistsl_tac [`u`, `G1`, `tn1`] >> simp[]
QED
