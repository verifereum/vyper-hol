(* TOP-LEVEL: complete indexed-topic production preserves older operands
   with reused SSA outputs. Helpers transport typed inputs and compose
   executions in source order. *)
Theory eventTopicsOperands
Ancestors
  vyperEventArgCompat
  eventTopicOperands eventTopicsExecProps eventLogSplitProps eventEncodingProps typedLogSplitArgs
  eventTopicValueProps eventTopicExecProps abiFieldOperands abiFlatRun
  context stmtLowering compileEnv exprLoweringProps emitHelperProps
  venomState venomExecSemantics vyperEvent list pair rich_list arithmetic
Libs pairLib

Theorem topic_values_operands_frame:
  !tenv args values ss out bound.
    LIST_REL (\arg v. topic_value_rel tenv arg v ss) args values /\
    EVERY (\arg. abi_operand_before bound (FST arg)) args /\ out with vs_vars := ss.vs_vars = ss /\
    (!old. abi_operand_before bound old ==> eval_operand old out = eval_operand old ss) ==>
    LIST_REL (\arg v. topic_value_rel tenv arg v out) args values
Proof
  Induct_on `args` >- simp[] >> rpt gen_tac >> Cases_on `values` >> simp[] >> strip_tac >>
  rename1 `topic_value_rel tenv arg value ss` >> PairCases_on `arg` >>
  rename1 `topic_value_rel tenv (ptr_op,ty) value ss` >>
  `out.vs_memory = ss.vs_memory` by (irule assignment_frame_memory >> first_assum MATCH_ACCEPT_TAC) >>
  `eval_operand ptr_op out = eval_operand ptr_op ss` by
    (qpat_x_assum `!old. abi_operand_before bound old ==> _` irule >> fs[]) >>
  `topic_value_rel tenv (ptr_op,ty) value out` by
    (drule_all topic_value_rel_operand_frame >> simp[]) >>
  simp[] >> first_x_assum irule >> qexistsl_tac [`bound`, `ss`] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem topic_execution_operand_cons:
  !cs mid cs' ss ss_mid out head_op tail_ops head_word tail_words.
    run_inst_seq (emitted_insts cs mid) ss = OK ss_mid /\
    eval_operand head_op ss_mid = SOME head_word /\ abi_operand_before mid.cs_next_var head_op /\
    same_blocks cs mid /\ cs.cs_next_var <= mid.cs_next_var /\
    (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old ss_mid = eval_operand old ss) /\
    ss_mid with vs_vars := ss.vs_vars = ss /\
    run_inst_seq (emitted_insts mid cs') ss_mid = OK out /\
    eval_operands tail_ops out = SOME tail_words /\ same_blocks mid cs' /\ mid.cs_next_var <= cs'.cs_next_var /\
    EVERY (abi_operand_before cs'.cs_next_var) tail_ops /\
    (!old. abi_operand_before mid.cs_next_var old ==> eval_operand old out = eval_operand old ss_mid) /\
    out with vs_vars := ss_mid.vs_vars = ss_mid /\
    mid.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs mid /\
    cs'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid cs' ==>
    run_inst_seq (emitted_insts cs cs') ss = OK out /\
    eval_operands (head_op::tail_ops) out = SOME (head_word::tail_words) /\
    same_blocks cs cs' /\ EVERY (abi_operand_before cs'.cs_next_var) (head_op::tail_ops) /\
    cs.cs_next_var <= cs'.cs_next_var /\
    (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
    out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  `run_inst_seq (emitted_insts cs cs') ss = OK out` by
    (mp_tac (Q.SPECL [`cs`, `mid`, `cs'`, `ss`, `ss_mid`, `out`] run_emitted_compose2) >> simp[]) >>
  `same_blocks cs cs'` by (irule same_blocks_trans >> qexists_tac `mid` >> simp[]) >>
  `abi_operand_before cs'.cs_next_var head_op` by
    (irule abi_operand_before_mono >> qexists_tac `mid.cs_next_var` >> simp[]) >>
  `eval_operand head_op out = SOME head_word` by
    (qpat_x_assum `!old. _ ==> eval_operand old out = _` (qspec_then `head_op` mp_tac) >> simp[]) >>
  `!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `mid.cs_next_var`, `ss`, `ss_mid`, `out`]
      abi_operand_before_frame_trans) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `out with vs_vars := ss.vs_vars = ss` by
    (irule assignment_frame_trans >> qexists_tac `ss_mid` >> simp[]) >>
  `cs.cs_next_var <= cs'.cs_next_var` by decide_tac >>
  asm_simp_tac (srw_ss()) [eval_operands_def] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_log_topic_operands:
  !tenv args values cs ops cs' ss.
    LIST_REL (\arg v. topic_value_rel tenv arg v ss) args values /\
    compile_log_topic_ops (MAP (\(arg_op,ty). (arg_op,is_bytestring_type ty)) args) cs = (ops,cs') /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args ==>
    ?out topics. run_inst_seq (emitted_insts cs cs') ss = OK out /\ eval_operands ops out = SOME topics /\
      encode_indexed_event_topics (REPLICATE (LENGTH args) T) (MAP SND args) values = SOME topics /\
      same_blocks cs cs' /\ EVERY (abi_operand_before cs'.cs_next_var) ops /\ cs.cs_next_var <= cs'.cs_next_var /\
      (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  Induct_on `args`
  >- (rpt gen_tac >> Cases_on `values` >> simp[compile_log_topic_ops_def, comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`ss`, `[]`] >> simp[emitted_insts_def, run_inst_seq_def, eval_operands_def,
        encode_indexed_event_topics_def, same_blocks_def]) >>
  rpt gen_tac >> Cases_on `values` >> simp[] >> strip_tac >>
  rename1 `topic_value_rel tenv arg value ss` >> PairCases_on `arg` >>
  rename1 `topic_value_rel tenv (arg_op,ty) value ss` >>
  qpat_x_assum `compile_log_topic_ops _ cs = (ops,cs')` mp_tac >>
  simp_tac (srw_ss()) [Once compile_log_topic_ops_def, comp_bind_def, comp_return_def, LET_THM] >>
  strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_encode_log_topic arg_op (is_bytestring_type ty) cs = (head_op,mid)` >>
  rename1 `compile_log_topic_ops _ mid = (tail_ops,cs')` >> rename1 `LIST_REL _ args tail_values` >>
  drule_all compile_topic_value_operands >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs mid) ss = OK ss_mid` >>
  `LIST_REL (\arg v. topic_value_rel tenv arg v ss_mid) args tail_values` by
    (irule topic_values_operands_frame >> qexistsl_tac [`cs.cs_next_var`, `ss`] >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `EVERY (\arg. abi_operand_before mid.cs_next_var (FST arg)) args` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> fs[EVERY_MEM]) >>
  qpat_x_assum `!tenv values cs ops cs' ss. _`
    (qspecl_then [`tenv`, `tail_values`, `mid`, `tail_ops`, `cs'`, `ss_mid`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts mid cs') ss_mid = OK final` >>
  rename1 `eval_operands tail_ops final = SOME tail_words` >>
  drule_all topic_value_rel_encodes >> strip_tac >> rename1 `encode_event_topic ty value = SOME head_word` >>
  `eval_operand head_op ss_mid = SOME head_word` by gvs[] >>
  `mid.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs mid` by
    (drule_all compile_topic_extends_insts >> simp[]) >>
  `cs'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid cs'` by
    (drule_all compile_topics_extends_insts >> simp[]) >>
  drule_all topic_execution_operand_cons >> strip_tac >>
  qexistsl_tac [`final`, `head_word::tail_words`] >> fs[encode_indexed_event_topics_def] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_split_log_topic_operands:
  !tenv flags args values field_types cs ops cs' ss.
    LENGTH flags = LENGTH args /\
    LIST_REL (\(flag,arg) v. flag ==> topic_value_rel tenv arg v ss) (ZIP (flags,args)) values /\
    LIST_REL event_arg_compatible field_types (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags field_types /\
    compile_log_topic_ops (FST (split_log_ops args flags)) cs = (ops,cs') /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args ==>
    ?out topics. run_inst_seq (emitted_insts cs cs') ss = OK out /\ eval_operands ops out = SOME topics /\
      encode_indexed_event_topics flags field_types values = SOME topics /\
      same_blocks cs cs' /\ EVERY (abi_operand_before cs'.cs_next_var) ops /\ cs.cs_next_var <= cs'.cs_next_var /\
      (!old. abi_operand_before cs.cs_next_var old ==> eval_operand old out = eval_operand old ss) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH values` by
    (qpat_x_assum `LIST_REL _ (ZIP (flags,args)) values` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     simp[LENGTH_ZIP, MIN_DEF]) >>
  `LIST_REL (\arg v. topic_value_rel tenv arg v ss)
    (select_log_args T flags args) (select_log_args T flags values)` by
    (irule select_log_args_rel >> simp[]) >>
  `EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) (select_log_args T flags args)` by
    (irule EVERY_select_log_args >> first_assum MATCH_ACCEPT_TAC) >>
  `split_log_ops args flags = (MAP (\(arg_op,ty). (arg_op,is_bytestring_type ty))
    (select_log_args T flags args), select_log_args F flags args)` by (irule split_log_ops_select >> simp[]) >>
  fs[] >> drule_all compile_log_topic_operands >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK final` >> rename1 `eval_operands ops final = SOME topics` >>
  `encode_indexed_event_topics flags (MAP SND args) values = SOME topics` by
    (mp_tac (Q.SPECL [`flags`, `MAP SND (args:(operand # type) list)`, `values`]
      encode_indexed_event_topics_select) >> simp[select_log_args_MAP]) >>
  `encode_indexed_event_topics flags field_types values = encode_indexed_event_topics flags (MAP SND args) values` by
    (irule compatible_indexed_event_topics >> simp[]) >>
  qexistsl_tac [`final`, `topics`] >> simp[] >> first_assum MATCH_ACCEPT_TAC
QED
