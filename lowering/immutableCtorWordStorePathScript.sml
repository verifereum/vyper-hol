Theory immutableCtorWordStorePath
Ancestors
  exprPtrCtorImmStore bodyImmutableStoreMemory immutableDeployOperandTransfer
  bodyFullUnwrapRun fragGasOriginPtrDead
  ptrDiscipline context compileEnv exprLoweringProps emitHelper emitHelperProps fragExec instSeqPtrLo
  venomState venomInst venomExecSemantics loweringStateRelDefs
  string ASCIInumbers rich_list pred_set list words arithmetic finite_map

Theorem immutable_ctor_word_store_segment[local]:
  compile_imm_store_word imm dst operand sa = ((),sb) /\
  eval_operand operand s = SOME value /\ op_taint tn operand = {} /\
  (!x. operand = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME a /\ op_taint tn dst = {} /\ op_prov G dst = NONE /\
  w2n a + 32 <= lo /\
  (!base. imm = SOME base ==> eval_operand base s = SOME 0w /\
    op_taint tn base = {} /\ op_prov G base = NONE) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  sb.cs_current_bb = sa.cs_current_bb /\ ~block_is_terminated sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  ?Gf tf u.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    (!k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
       (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tf.t_imm = key_update tn.t_imm (w2n a) {} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >> namedCases_on `imm` ["","base_op"] >>
  qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_store_word_def, emit_op_def, emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[Excl "APPEND_ASSOC", GSYM APPEND_ASSOC, emitted_insts_def, DROP_APPEND2] >>
  (conj_tac >- (Cases_on `sa.cs_current_insts` >>
    simp[block_is_terminated_def, LAST_CONS_cond, mk_inst_def, is_terminator_def])) >>
  simp[is_terminator_def]
  >- (mp_tac (Q.INST [`arg` |-> `dst`, `v` |-> `operand`, `id` |-> `sa.cs_next_id`,
        `fn` |-> `func`, `PG` |-> `PG`, `D` |-> `D`] ctor_istore_segment) >>
      impl_tac >- simp[] >> strip_tac >>
      qexistsl [`Gf`,`tnf`,`t`] >> simp[]) >>
  `!p. not_fresh_at sa p ==> p <> STRING #"%" (toString sa.cs_next_var)` by
    simp[not_fresh_at_def] >>
  `!x. operand = Var x ==> x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  mp_tac (Q.INST [`P` |-> `not_fresh_at sa`, `v` |-> `operand`,
    `region:operand` |-> `base_op:operand`, `id` |-> `sa.cs_next_id`, `fn` |-> `func`,
    `tmp` |-> `STRING #"%" (toString sa.cs_next_var)`] ctor_word_store_seq) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qexistsl [`Gf`,`tnf`,`t`] >> simp[]
QED

Theorem immutable_ctor_word_store_path:
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
  qabbrev_tac `D0 = <| d_stor := K (K {}); d_trans := K (K {});
    d_imm := K {}; d_ret := K {} |>` >>
  drule_all immutable_ctor_word_store_segment >>
  disch_then (qspecl_then [`func`,`PG`,`D0`] strip_assume_tac) >>
  `!base. imm = SOME base ==> eval_operand base s = SOME 0w` by metis_tac[] >>
  `w2n a + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all immutable_store_word_mem_ok >> strip_tac >>
  drule_all immutable_store_word_old_execution >> strip_tac >>
  `t = u` by metis_tac[exec_result_11] >>
  qpat_x_assum `t = u` (SUBST_ALL_TAC o SYM) >>
  `inst_seq_ptr D0 lo ctx func PG G tn (emitted_insts sa sb) s Gf tf` by
    (qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` (ACCEPT_TAC o REWRITE_RULE [venom_state_fupdselfid]))) >>
  `gas_origin_ptr_path (D0,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)` by
    (irule emitted_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts sa sb`,`sa`] >> simp[]) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gf`,`tf`,`t`] >> simp[IgnAsm `sb.cs_current_insts = _`] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  qunabbrev_tac `D0` >> first_assum ACCEPT_TAC
QED
