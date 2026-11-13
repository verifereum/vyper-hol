(* Fixed RawLog suffix: path and frame at one horizon-uniform endpoint. *)
Theory bodyFullRawLogFixedTail
Ancestors bodyFullRawLogFixedTailPath bodyFullRawLogFixedTailFrame

Theorem raw_log_fixed_tail_full:
  !buf data_op sm s1 ops sb alloc_sa data_sa func cenv ctx sa data ann es_call dflt
      cx st0 ee DF lo explicit PG es s0 bs s G tn G0 tn0 d word p w vals.
    emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
    emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
    compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    LENGTH ops < dimword (:256) /\ sa.cs_next_id <= alloc_sa.cs_next_id /\
    sa.cs_next_var <= sm.cs_next_var /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) (buf.buf_operand::data_op::ops) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    expr_type data = BaseT (BytesT (Fixed 32)) /\ post_value_type cenv data = expr_type data /\
    expr_type (Call ann RawLog es_call dflt) = NoneT /\
    post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
    expr_has_effect (Call ann RawLog es_call dflt) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
      expr_store_bound cx (expr_type data) (BytesV bs) data_op s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
      ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G tn s /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func s /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ LENGTH bs = 32 /\
      eval_operand data_op s = SOME word /\ TAKE 32 (word_to_bytes_be word) = bs /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand s = SOME w /\ ptr_covers G tn p s 32 /\
      FLOOKUP s.vs_allocas alloc_sa.cs_next_id = SOME (w2n w,32) /\ w2n w + 32 < dimword (:256) /\
      (!name b n. local_region cenv ee.scopes s name b n ==> regions_disjoint (w2n w) 32 b n) /\
      (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
        regions_disjoint (w2n w) 32 b n) /\
      eval_operands ops s = SOME (MAP event_value_to_word vals) /\
      EVERY (\op. op_taint tn op = {}) ops /\ ~s.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts) ==>
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2) /\
      expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) u /\
      expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx
        (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G2 tn2 u /\
      (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
        ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G2 u) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  drule_all raw_log_fixed_tail_path >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `u` (qx_choose_then `G2`
      (qx_choose_then `tn2` assume_tac)))) >>
  qexistsl [`u`, `G2`, `tn2`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _ = _ /\ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  drule_all raw_log_fixed_tail_post_frame >> strip_tac >> simp[]
QED
