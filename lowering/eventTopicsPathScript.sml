(* TOP-LEVEL: execute actual indexed-topic production from the saved
   arguments. Source topics, final control, RAM, allocator state and old
   operands are derived by compile_split_log_topics_path.
   Helper: split_topic_operands_before. *)
Theory eventTopicsPath
Ancestors
  vyperEventArgCompat
  eventTopicCode eventTopicsOperands eventLogSplitProps eventTopicsExecProps eventTopicExecProps eventTopicValueProps
  typedLogSplitArgs typedCopyStateFrame abiFieldOperands
  stmtLowering context compileEnv exprLoweringProps fragExec fragBlockPath instIdxIndep
  venomExecSemantics venomState venomInst vyperEvent list pair words

Theorem split_topic_operands_before:
  !args flags bound.
    LENGTH flags = LENGTH args /\ EVERY (\arg. abi_operand_before bound (FST arg)) args ==>
    EVERY (\arg. abi_operand_before bound (FST arg)) (FST (split_log_ops args flags))
Proof
  rpt gen_tac >> strip_tac >> drule split_log_ops_select >> DISCH_TAC >>
  `EVERY (\arg. abi_operand_before bound (FST arg)) (select_log_args T flags args)` by
    (irule EVERY_select_log_args >> first_assum MATCH_ACCEPT_TAC) >>
  fs[EVERY_MAP, EVERY_MEM, FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP, EXISTS_PROD] >>
  qpat_x_assum `!p_1 p_2. MEM (p_1,p_2) (select_log_args T flags args) ==> _` drule_all >> simp[]
QED

Theorem compile_split_log_topics_path:
  !ctx func tenv flags args values field_types cs ops cs' ss.
    LENGTH flags = LENGTH args /\
    LIST_REL (\(flag,arg) v. flag ==> topic_value_rel tenv arg v ss) (ZIP (flags,args)) values /\
    LIST_REL event_arg_compatible field_types (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags field_types /\
    compile_log_topic_ops (FST (split_log_ops args flags)) cs = (ops,cs') /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out topics. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operands ops out = SOME topics /\ encode_indexed_event_topics flags field_types values = SOME topics /\
      EVERY (abi_operand_before cs'.cs_next_var) ops /\ cs.cs_next_var <= cs'.cs_next_var /\
      copy_state_frame ss out /\ out.vs_memory = ss.vs_memory /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all split_topic_operands_before >> DISCH_TAC >>
  mp_tac (Q.SPECL [`FST (split_log_ops args flags)`, `cs`, `ops`, `cs'`] compile_topics_code) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  drule_all_then (qx_choose_then `raw` (qx_choose_then `topics` strip_assume_tac)) compile_split_log_topic_operands >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`, `raw`] fragment_path_emitted) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `copy_state_frame ss raw` by
    (mp_tac (Q.SPECL [`ss`, `raw`, `ss.vs_inst_idx`] copy_state_frame_var_image) >> simp[]) >>
  `raw.vs_memory = ss.vs_memory` by (drule assignment_frame_memory >> simp[]) >>
  `raw.vs_halted = ss.vs_halted` by
    (qpat_x_assum `raw with vs_vars := _ = ss`
       (mp_tac o AP_TERM ``\state:venom_state. state.vs_halted``) >> simp[]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op raw = eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >>
     mp_tac (Q.SPECL [`emitted_insts cs cs'`, `ss`, `raw`, `arg_op`] run_inst_seq_operand_frame) >>
     impl_tac >- fs[EVERY_CONJ] >> simp[]) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH cs'.cs_current_insts`, `topics`] >>
  simp[eval_op_inst_idx, eval_ops_inst_idx]
QED
