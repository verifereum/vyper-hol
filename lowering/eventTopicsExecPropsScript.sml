(* TOP-LEVEL: execution of the complete indexed-topic compiler in source order.
   Typed inputs include their actual payload footprint. The execution frame
   preserves all earlier operands, input representations, and payload memory. *)
Theory eventTopicsExecProps
Ancestors
  eventTopicValueProps eventTopicExecProps eventLoweringStructure
  exprLoweringProps nameLoweringProps emitHelperProps stmtLowering compileEnv
  venomState venomExecSemantics vyperEvent list rich_list
Libs pairLib

Theorem eval_operands_preserve_success:
  !ops ss out values.
    eval_operands ops ss = SOME values /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) ==>
    eval_operands ops out = SOME values
Proof
  Induct_on `ops` >- simp[eval_operands_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `eval_operands (arg_op::rest) ss = SOME values` >>
  qpat_x_assum `eval_operands (arg_op::rest) ss = SOME values` mp_tac >>
  simp_tac (srw_ss()) [Once eval_operands_def] >>
  Cases_on `eval_operand arg_op ss` >> simp[] >>
  Cases_on `eval_operands rest ss` >> simp[] >> strip_tac >> gvs[] >>
  rename1 `eval_operand arg_op ss = SOME value_head` >>
  rename1 `eval_operands rest ss = SOME values_tail` >>
  `eval_operand arg_op out = SOME value_head` by
    (qpat_x_assum `!old w. eval_operand old ss = SOME w ==> _` irule >> simp[]) >>
  `eval_operands rest out = SOME values_tail` by
    (qpat_x_assum `!ss out values. _`
       (qspecl_then [`ss`, `out`, `values_tail`] mp_tac) >> simp[]) >>
  simp[Once eval_operands_def]
QED

Theorem topic_values_assignment_frame:
  !tenv args values ss out.
    LIST_REL (\arg v. topic_value_rel tenv arg v ss) args values /\
    out with vs_vars := ss.vs_vars = ss /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) ==>
    LIST_REL (\arg v. topic_value_rel tenv arg v out) args values
Proof
  rpt gen_tac >> strip_tac >> irule LIST_REL_mono >>
  qexists_tac `\arg v. topic_value_rel tenv arg v ss` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `topic_value_rel tenv arg value ss` >> Cases_on `arg` >>
  irule topic_value_rel_assignment_frame >> qexists_tac `ss` >> simp[]
QED

Theorem compile_topic_extends_insts:
  !arg_op flag cs op cs'.
    compile_encode_log_topic arg_op flag cs = (op,cs') /\ same_blocks cs cs' ==>
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs'
Proof
  rpt strip_tac >>
  `ci_mono cs cs'` by
    (mp_tac (Q.SPECL [`arg_op`, `flag`, `cs`] compile_encode_log_topic_ci_mono) >>
     simp[]) >>
  `isPREFIX cs.cs_current_insts cs'.cs_current_insts` by
    gvs[ci_mono_def, same_blocks_def, cs_extends_def, APPEND_EQ_SELF] >>
  gvs[GSYM prefix_drop_equiv, emitted_insts_def]
QED

Theorem compile_topics_extends_insts:
  !args cs ops cs'.
    compile_log_topic_ops args cs = (ops,cs') /\ same_blocks cs cs' ==>
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs'
Proof
  rpt strip_tac >>
  `ci_mono cs cs'` by
    (mp_tac (Q.SPECL [`args`, `cs`] compile_log_topic_ops_ci_mono) >> simp[]) >>
  `isPREFIX cs.cs_current_insts cs'.cs_current_insts` by
    gvs[ci_mono_def, same_blocks_def, cs_extends_def, APPEND_EQ_SELF] >>
  gvs[GSYM prefix_drop_equiv, emitted_insts_def]
QED

Theorem assignment_execution_compose:
  !cs mid cs' ss ss_mid out.
    run_inst_seq (emitted_insts cs mid) ss = OK ss_mid /\
    same_blocks cs mid /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss_mid = SOME w) /\
    ss_mid with vs_vars := ss.vs_vars = ss /\
    run_inst_seq (emitted_insts mid cs') ss_mid = OK out /\
    same_blocks mid cs' /\
    fresh_vars_wrt cs' out /\
    (!old w. eval_operand old ss_mid = SOME w ==> eval_operand old out = SOME w) /\
    out with vs_vars := ss_mid.vs_vars = ss_mid /\
    mid.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs mid /\
    cs'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid cs' ==>
    run_inst_seq (emitted_insts cs cs') ss = OK out /\
    same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
    out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (mp_tac (Q.SPECL [`cs`, `mid`, `cs'`, `ss`, `ss_mid`, `out`]
        run_emitted_compose2) >> simp[]) >>
  conj_tac >- (irule same_blocks_trans >> qexists_tac `mid` >> simp[]) >>
  conj_tac >- simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `eval_operand old ss_mid = SOME w` by
        (qpat_x_assum `!old w. eval_operand old ss = SOME w ==> _` irule >> simp[]) >>
      qpat_x_assum `!old w. eval_operand old ss_mid = SOME w ==> _` irule >> simp[]) >>
  irule assignment_frame_trans >> qexists_tac `ss_mid` >> simp[]
QED

Theorem topic_execution_cons:
  !cs mid cs' ss ss_mid out head_op tail_ops head_word tail_words.
    run_inst_seq (emitted_insts cs mid) ss = OK ss_mid /\
    eval_operand head_op ss_mid = SOME head_word /\ same_blocks cs mid /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old ss_mid = SOME w) /\
    ss_mid with vs_vars := ss.vs_vars = ss /\
    run_inst_seq (emitted_insts mid cs') ss_mid = OK out /\
    eval_operands tail_ops out = SOME tail_words /\ same_blocks mid cs' /\
    fresh_vars_wrt cs' out /\
    (!old w. eval_operand old ss_mid = SOME w ==> eval_operand old out = SOME w) /\
    out with vs_vars := ss_mid.vs_vars = ss_mid /\
    mid.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs mid /\
    cs'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid cs' ==>
    run_inst_seq (emitted_insts cs cs') ss = OK out /\
    eval_operands (head_op::tail_ops) out = SOME (head_word::tail_words) /\
    same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
    (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
    out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`cs`, `mid`, `cs'`, `ss`, `ss_mid`, `out`]
    assignment_execution_compose) >> simp[] >> strip_tac >> simp[] >>
  `eval_operand head_op out = SOME head_word` by
    (qpat_x_assum `!old w. eval_operand old ss_mid = SOME w ==> _` irule >> simp[]) >>
  simp[eval_operands_def]
QED

Theorem compile_log_topic_ops_correct:
  !tenv args values cs ops cs' ss.
    LIST_REL (\arg v. topic_value_rel tenv arg v ss) args values /\
    compile_log_topic_ops
      (MAP (\(arg_op,ty). (arg_op,is_bytestring_type ty)) args) cs = (ops,cs') /\
    fresh_vars_wrt cs ss ==>
    ?out topics.
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operands ops out = SOME topics /\
      encode_indexed_event_topics (REPLICATE (LENGTH args) T)
        (MAP SND args) values = SOME topics /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  Induct_on `args`
  >- (rpt gen_tac >> Cases_on `values` >>
      simp[compile_log_topic_ops_def, comp_return_def] >> strip_tac >> gvs[] >>
      qexistsl_tac [`ss`, `[]`] >>
      simp[emitted_insts_def, run_inst_seq_def, eval_operands_def,
        encode_indexed_event_topics_def, same_blocks_def]) >>
  rpt gen_tac >> Cases_on `values` >> simp[] >> strip_tac >>
  rename1 `topic_value_rel tenv arg value ss` >> PairCases_on `arg` >>
  rename1 `topic_value_rel tenv (arg_op,ty) value ss` >>
  qpat_x_assum `compile_log_topic_ops _ cs = (ops,cs')` mp_tac >>
  simp_tac (srw_ss()) [Once compile_log_topic_ops_def, comp_bind_def, comp_return_def,
    LET_THM] >>
  strip_tac >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_encode_log_topic arg_op (is_bytestring_type ty) cs = (head_op,mid)` >>
  rename1 `compile_log_topic_ops _ mid = (tail_ops,cs')` >>
  rename1 `LIST_REL _ args tail_values` >>
  drule_all compile_topic_value_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs mid) ss = OK ss_mid` >>
  `LIST_REL (\arg v. topic_value_rel tenv arg v ss_mid) args tail_values` by
    (irule topic_values_assignment_frame >> qexists_tac `ss` >> simp[]) >>
  qpat_x_assum `!tenv values cs ops cs' ss. _`
    (qspecl_then [`tenv`, `tail_values`, `mid`, `tail_ops`, `cs'`, `ss_mid`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts mid cs') ss_mid = OK final` >>
  rename1 `eval_operands tail_ops final = SOME tail_words` >>
  drule_all topic_value_rel_encodes >> strip_tac >>
  rename1 `encode_event_topic ty value = SOME head_word` >>
  `eval_operand head_op ss_mid = SOME head_word` by gvs[] >>
  `mid.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs mid` by
    (drule_all compile_topic_extends_insts >> simp[]) >>
  `cs'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid cs'` by
    (drule_all compile_topics_extends_insts >> simp[]) >>
  drule_all topic_execution_cons >> strip_tac >>
  qexistsl_tac [`final`, `head_word::tail_words`] >>
  simp[encode_indexed_event_topics_def]
QED

(* This producer runs the actual source name load and subsequent topic hash.
   It does not assume execution or encoding correctness for either compiler. *)
Theorem compile_name_topic_correct:
  !env cenv cx func ty ann id es ss cs arg_op mid topic_op cs' p region_size.
    well_typed_expr env (Name ann id) /\ env_consistent env cx es /\
    state_well_typed es /\ state_rel_simple cenv cx es ss /\
    local_ptrs_rel func cenv es.scopes ss /\ event_indexable_type ann /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) region_size) /\
    (is_bytestring_type ann ==> ss.vs_alloca_next <= dimword(:256)) /\
    fresh_vars_wrt cs ss /\
    lower_value compile_expr cenv ty (Name ann id) cs = (arg_op,mid) /\
    compile_encode_log_topic arg_op (is_bytestring_type ann) mid = (topic_op,cs') ==>
    ?v out.
      eval_expr cx (Name ann id) es = (INL (Value v),es) /\
      run_inst_seq (emitted_insts cs cs') ss = OK out /\
      eval_operand topic_op out = encode_event_topic ann v /\
      same_blocks cs cs' /\ fresh_vars_wrt cs' out /\
      state_rel_simple cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      out with vs_vars := ss.vs_vars = ss
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`env`, `cenv`, `cx`, `func`, `ty`, `ann`, `id`, `es`, `ss`,
    `cs`, `arg_op`, `mid`, `p`, `region_size`] compile_name_topic_value_correct) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs mid) ss = OK ss_mid` >>
  rename1 `topic_value_rel env.type_defs (arg_op,ann) value ss_mid` >>
  drule_all compile_topic_value_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts mid cs') ss_mid = OK final` >>
  `mid.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs mid` by
    (drule_all compile_expr_extends_insts >> simp[]) >>
  `cs'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid cs'` by
    (drule_all compile_topic_extends_insts >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `mid`, `cs'`, `ss`, `ss_mid`, `final`]
    assignment_execution_compose) >> simp[] >> strip_tac >>
  conj_tac >>
  FIRST [irule state_rel_simple_assignment_frame >> qexists_tac `ss_mid` >> simp[],
         irule local_ptrs_rel_assignment_frame >> qexists_tac `ss_mid` >> simp[]]
QED
