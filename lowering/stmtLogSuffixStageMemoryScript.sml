(* Selected arguments at the post-topic memory boundary. *)
Theory stmtLogSuffixStageMemory
Ancestors
  stmtSimLogSuffix stmtSimLogTrace stmtSimLogTopicFresh stmtSimLogTopics loweringStateRelDefs
  stmtLogDataMemory abiDecoderReentry compileEnv exprLoweringProps
  emitHelperProps abiEncoderCounters abiEncoderAppend list words
  loweringHalt stmtSimLogDataRun fragExec abiBuiltinAllocation
  fragExecMem instMemFrontier venomMemDefs venomInst

Theorem log_mem_selected_typed:
  !xs vs flags.
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  LENGTH flags = LENGTH xs /\
  LIST_REL (log_arg_rel ce cx sa st es t)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) ==>
  LIST_REL (\arg v. log_arg_rel ce cx sa st es t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)
Proof
  rpt gen_tac >> strip_tac >> drule_all split_log_ops_data_rel >>
  qpat_abbrev_tac `ds = SND (split_log_ops xs flags)` >>
  qpat_abbrev_tac `ws = log_non_indexed_values flags vs` >>
  qpat_x_assum `LIST_REL _ xs vs` kall_tac >>
  qpat_x_assum `Abbrev (ds = _)` kall_tac >>
  qpat_x_assum `Abbrev (ws = _)` kall_tac >>
  qpat_x_assum `LIST_REL _ ds ws` mp_tac >>
  qid_spec_tac `ws` >> qid_spec_tac `ds` >>
  Induct >> Cases_on `ws` >> simp[] >> metis_tac[]
QED

Theorem log_mem_selected_frontier:
  LENGTH flags = LENGTH xs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) ==>
  cs_extends sm st /\ sm.cs_next_var <= st.cs_next_var /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at st z) /\ (!l. FST p <> Label l))
    (SND (split_log_ops xs flags)) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) (Lit (n2w h)::ops)
Proof
  strip_tac >>
  `EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l))
    (FST (split_log_ops xs flags))` by
    (drule_all log_indexed_selection_every >>
     drule_all split_log_ops_select >> strip_tac >>
     simp[MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP]) >>
  drule_all compile_log_topic_ops_frontier >> strip_tac >>
  drule_all log_split_data_every >> strip_tac >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[EVERY_MEM, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      not_fresh_at_def] >> rpt strip_tac >> Cases_on `e` >> gvs[] >> metis_tac[]
QED

Theorem log_mem_rounded_transport:
  !xs vs. LIST_REL (\arg v. !w n.
    ~is_word_type (SND arg) /\ eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= s.vs_alloca_next) xs vs /\
  EVERY (\arg. eval_operand (FST arg) u = eval_operand (FST arg) s) xs /\
  s.vs_alloca_next <= u.vs_alloca_next ==>
  LIST_REL (\arg v. !w n.
    ~is_word_type (SND arg) /\ eval_operand (FST arg) u = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= u.vs_alloca_next) xs vs
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem log_mem_selected_rounded:
  LENGTH flags = LENGTH xs /\
  LIST_REL (\arg v. !w n.
    ~is_word_type (SND arg) /\ eval_operand (FST arg) s = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= s.vs_alloca_next) xs vs /\
  EVERY (\arg. eval_operand (FST arg) u = eval_operand (FST arg) s)
    (SND (split_log_ops xs flags)) /\
  s.vs_alloca_next <= u.vs_alloca_next ==>
  LIST_REL (\arg v. !w n.
    ~is_word_type (SND arg) /\ eval_operand (FST arg) u = SOME w /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
     (?str. v = StringV str /\ n = LENGTH str)) ==>
    w2n w + 32 + 32 * ((n+31) DIV 32) <= u.vs_alloca_next)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)
Proof
  strip_tac >> drule_all split_log_ops_data_rel >> strip_tac >>
  irule log_mem_rounded_transport >> goal_assum (drule_at Any) >> simp[]
QED

Theorem log_mem_data_stage_code:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs src.buf_operand 0 s1 = ((),s2) /\
  EVERY (supported_scalar_type o SND) xs /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func /\ sb.cs_next_var <= limit_st.cs_next_var ==>
  fn_has_code st s1 func /\ fn_has_code s2 s3 func /\
  fn_has_code s3 s4 func /\ s4.cs_next_var <= limit_st.cs_next_var
Proof
  strip_tac >>
  imp_res_tac compile_alloc_buffer_extends >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `cs_extends s1 s2` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  drule cs_extends_abi_encode >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s4 sb` by
    (irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
  `cs_extends sm s1` by (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
  `cs_extends sm s2` by (irule cs_extends_trans >> qexists_tac `s1` >> simp[]) >>
  `cs_extends sm s3` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  `cs_extends s3 sb` by (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `cs_extends s2 sb` by (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `cs_extends s1 sb` by (irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  rpt conj_tac
  >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule fn_has_code_mid >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem log_mem_alloc_check:
  compile_alloc_buffer cap st = (buf,st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges, mk_inst_def]
QED

Theorem log_mem_alloc_frame_bounds:
  abi_builtin_allocation_frame next site cap s t /\
  alloca_next_valid t /\ FLOOKUP t.vs_allocas site = SOME (p,cap) ==>
  s.vs_alloca_next <= t.vs_alloca_next /\ p+cap <= t.vs_alloca_next
Proof
  strip_tac >> reverse conj_tac
  >- metis_tac[alloca_next_valid_def] >>
  gvs[abi_builtin_allocation_frame_def, abi_builtin_allocate_state_def] >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >> gvs[]
QED
