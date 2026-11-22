(* Constructor word store to a compiled pointer, with its memory and ghost frames. *)
Theory immutableWordStorePath
Ancestors
  immutableDeployOperandTransfer bodyImmutableStoreMemory exprPtrCtorImmStore
  exprLoweringProps exprSimCopy emitHelper emitHelperProps fragGasSeqPtr
  immutableCopyExecution fragGasOriginPtr fragExecMem fragExec
  codegenRel venomExecSemantics venomState venomInst exprLowering
  loweringStateRelDefs bodyPtrDefs ptrDiscipline context list finite_map compileEnv
  stmtReasonLitFragMemory fragGasOriginPtrDead arithmetic

Theorem immutable_word_store_path_with_execution[local]:
  compile_imm_store_word imm dst v sa = ((),sb) /\
  copy_old_operand sa v /\ eval_operand v s = SOME value /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
     op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gf tf.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf) /\
    same_blocks sa sb /\
    EVERY (\i. MEM i.inst_opcode [ADD; ISTORE]) (emitted_insts sa sb) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    u.vs_memory = (mstore (w2n a) value s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (w2n a,value) /\
    tf.t_mem =
      (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
        {w2n a + k | k IN op_taint tn v} /\
    tf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tf p u n)
Proof
  strip_tac >>
  drule_all immutable_word_store_segment >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `!x. v = Var x ==> not_fresh_at sa x` by fs[copy_old_operand_def] >>
  `!base. imm = SOME base ==> eval_operand base s = SOME 0w` by simp[] >>
  drule_all immutable_store_word_old_execution >> strip_tac >>
  gvs[immutable_execution_frame_def, Excl "GSYM"] >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  rename1 `tf.t_stor = tn.t_stor` >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ _ Gf tf` >>
  `w2n a + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all bodyImmutableStoreMemoryTheory.immutable_store_word_mem_ok >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ _`
       (drule_then strip_assume_tac) >> simp[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  `(ctx_has_dalloca ctx ==>
     !pre i post u. emitted_insts sa sb = pre ++ i::post /\
       run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >>
     `MEM i (emitted_insts sa sb)` by simp[] >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = ISTORE) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> Cases_on `i.inst_opcode` >> simp[]) >>
  qexistsl_tac [`Gf`,`tf`] >> simp[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem immutable_word_store_path:
  compile_imm_store_word imm dst v sa = ((),sb) /\
  copy_old_operand sa v /\ eval_operand v s = SOME value /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
     op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u Gf tf.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf) /\
    same_blocks sa sb /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_immutables := s.vs_immutables|>) = s /\
    u.vs_memory = (mstore (w2n a) value s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (w2n a,value) /\
    tf.t_mem =
      (tn.t_mem DIFF {j | w2n a <= j /\ j < w2n a + 32}) UNION
        {w2n a + k | k IN op_taint tn v} /\
    tf.t_imm = key_update tn.t_imm (w2n a) (op_taint tn v) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tf p u n)
Proof
  strip_tac >> drule_all immutable_word_store_path_with_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >> simp[]
QED

Theorem immutable_word_store_path_clean:
  compile_imm_store_word imm dst operand sa = ((),sb) /\
  eval_operand operand s = SOME value /\ op_taint tn operand = {} /\
  (!x. operand = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
    op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  sb.cs_current_bb = sa.cs_current_bb /\ ~block_is_terminated sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  ?Gf tf u.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_immutables := s.vs_immutables|>) = s /\
    u.vs_memory = (mstore (w2n a) value s).vs_memory /\
    u.vs_immutables = s.vs_immutables |+ (w2n a,value) /\
    tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tf.t_imm = key_update tn.t_imm (w2n a) {} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  `copy_old_operand sa operand` by simp[copy_old_operand_def] >>
  qabbrev_tac `D0 = <| d_stor := K (K {}); d_trans := K (K {});
    d_imm := K {}; d_ret := K {} |>` >>
  drule_all immutable_word_store_path_with_execution >>
  disch_then (qspecl_then [`explicit`,`PG`,`D0`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> gen_tac >> disch_tac >>
     qpat_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `~block_is_terminated sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (Cases_on `imm` >>
     qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_store_word_def,emit_op_def,emit_void_def,fresh_id_def,
          fresh_var_def,emit_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     strip_tac >> gvs[Excl "APPEND_ASSOC",GSYM APPEND_ASSOC,emitted_insts_def,DROP_APPEND2] >>
     Cases_on `sa.cs_current_insts` >>
     simp[block_is_terminated_def,LAST_CONS_cond,mk_inst_def,is_terminator_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  qunabbrev_tac `D0` >> fs[]
QED
