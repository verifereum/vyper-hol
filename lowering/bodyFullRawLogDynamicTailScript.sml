(* Horizon-uniform dynamic RawLog tail. *)
Theory bodyFullRawLogDynamicTail
Ancestors
  bodyFullRawLogDynamicPrepare bodyFullRawLogDynamicLog bodyFullRawLogDynamicData
  exprSimHashBoundary fragGasSeqPtr bodyFullGhostFrame
  exprLoweringProps loweringPosts bodyPtrDefs
  words list rich_list finite_map arithmetic

Theorem raw_log_dynamic_tail_full:
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
  ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2) /\
    expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs])
      NoneV (Lit 0w) u /\
    expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx
      (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
    ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
    (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
      ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
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
      cheat) >>
  gvs[]
QED
