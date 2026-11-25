(* The static LOG terminates at the fetch after the successful store. *)
Theory entryCreateRawLogFixedAbort
Ancestors
  bodyFullRawLogFixedTailPath entryCreatePathScope fragGasOriginPtr
  fragGasOrigin exprLoweringProps venomExecSemantics relation rich_list
  createSizePrefixReplay createMarkedPath fragExec

Theorem raw_log_fixed_abort_scope[local]:
  sb.cs_current_insts = sm.cs_current_insts ++ [i;j] /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  t1.vs_inst_idx = SUC s.vs_inst_idx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_id IN frag_ids sm sb /\
  gas_origin_edge T explicit ctx func s [] (OK t1) /\
  gas_origin_edge T explicit ctx func t1 [] (Abort ExHalt_abort u) ==>
  create_operand_full_scope sm sb explicit ctx func s [] (Abort ExHalt_abort u)
Proof
  strip_tac >>
  `s.vs_inst_idx <> LENGTH sb.cs_current_insts /\
   t1.vs_inst_idx <> LENGTH sb.cs_current_insts` by (simp[] >> decide_tac) >>
  `gas_origin_edge F explicit ctx func s [] (OK t1)` by
    (qpat_x_assum `gas_origin_edge T _ _ _ _ _ (OK _)` mp_tac >>
     simp[gas_origin_edge_def] >> metis_tac[]) >>
  `create_expr_prefix sm sb explicit ctx func s [] t1` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def, create_prefix_step_def] >>
     metis_tac[]) >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`, `last` |-> `[]`]
    create_operand_full_scope_terminal)) >>
  simp[exit_result_def] >> qexists_tac `t1` >> simp[]
QED

Theorem create_raw_log_fixed_tail_scoped_abort:
  !buf data_op sm s1 ops sb alloc_sa data_sa func cenv ctx sa data ann es_call dflt
      cx st0 ee DF lo explicit PG es s0 bs s G tn G0 tn0 d word p w vals.
    (cx.txn.is_static /\
     emit_void MSTORE [buf.buf_operand;data_op] sm = ((),s1) /\
     emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
     compile_alloc_buffer 32 alloc_sa = (buf,data_sa) /\ fn_has_code alloc_sa data_sa func /\
     fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
       s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts)) /\
    EVERY (\i. i.inst_id IN frag_ids sm sb) (emitted_insts sm sb) ==>
    ?u G2 tn2. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort ExHalt_abort u,G2,tn2) /\
      create_operand_full_scope sm sb explicit ctx func s [] (Abort ExHalt_abort u)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2
    (qspecl_then [`explicit`, `PG`] strip_assume_tac o
     MATCH_MP raw_log_fixed_static_tail_path_witness) assume_tac) >>
  qexistsl [`u`, `G2`, `tn2`] >> rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >> strip_tac >> simp[] >>
  irule raw_log_fixed_abort_scope >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND]
QED
