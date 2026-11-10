(* Operational absence preservation for topic-generated variable names. *)
Theory stmtSimLogTopicFresh
Ancestors
  stmtSimLogTopics freshWrites exprLoweringProps emitHelper emitHelperProps
  context stmtLowering compileEnv loweringStateRelDefs venomExecSemantics venomInst venomState
  words list rich_list arithmetic finite_map ASCIInumbers

Theorem log_topic_outputs[local]:
  compile_encode_log_topic op flag sa = (out,sb) /\ sb.cs_next_var <= nv ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; SHA3] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
      i.inst_outputs) (emitted_insts sa sb)
Proof
  Cases_on `flag` >>
  simp[compile_encode_log_topic_def, comp_return_def, emit_op_def,
    comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> rpt conj_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem log_topic_step_var[local]:
  MEM inst.inst_opcode [ADD; MLOAD; SHA3] /\
  step_inst_base inst s = OK t /\ ~MEM x inst.inst_outputs ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  fs[] >> simp[step_inst_base_opcode_eqs] >> strip_tac
  >>~- ([`exec_pure2 _ _ _ = OK _`],
    drule (cj 2 exec_pure_ok_update) >> strip_tac >>
    gvs[update_var_def, FLOOKUP_UPDATE]) >>
  gvs[exec_read1_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED

Theorem log_topic_code_var[local]:
  !code s t x. EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; SHA3] /\
    ~MEM x i.inst_outputs) code /\ run_inst_seq code s = OK t ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_at (Pat `step_inst_base _ _ = _`) log_topic_step_var >> simp[] >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_topics_counters[local]:
  !raw sa ops sb. compile_log_topic_ops raw sa = (ops,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  Induct_on `raw`
  >- simp[compile_log_topic_ops_def, comp_return_def] >>
  simp[compile_log_topic_ops_cons] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `compile_encode_log_topic _ _ _ = _` mp_tac >>
  Cases_on `SND h` >>
  simp[compile_encode_log_topic_def, comp_return_def, emit_op_def,
    comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem log_topics_outputs[local]:
  !raw sa ops sb nv. compile_log_topic_ops raw sa = (ops,sb) /\
    sb.cs_next_var <= nv ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; SHA3] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
      i.inst_outputs) (emitted_insts sa sb)
Proof
  Induct_on `raw`
  >- simp[compile_log_topic_ops_def, comp_return_def, emitted_insts_def] >>
  simp[compile_log_topic_ops_cons] >> rpt strip_tac >> gvs[] >>
  drule log_topics_counters >> strip_tac >>
  `sm.cs_next_var <= nv` by decide_tac >>
  drule_all log_topic_outputs >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule log_topic_inst_extends >> strip_tac >>
  drule log_topics_inst_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  gvs[]
QED

Theorem log_topics_fresh:
  compile_log_topic_ops raw sm = (ops,sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule_all log_topics_outputs >> strip_tac >>
  simp[fresh_vars_wrt_def] >> rpt strip_tac >>
  `FLOOKUP t.vs_vars (STRING #"%" (toString n)) =
   FLOOKUP s.vs_vars (STRING #"%" (toString n))` by
    (irule log_topic_code_var >> goal_assum (drule_at Any) >>
     qpat_x_assum `EVERY _ (emitted_insts sm sb)` mp_tac >>
     simp[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> simp[] >>
     qpat_x_assum `!x. MEM x _.inst_outputs ==> _` drule >> strip_tac >>
     gvs[toString_inj] >> decide_tac) >>
  `STRING #"%" (toString n) NOTIN FDOM s.vs_vars` by
    (fs[fresh_vars_wrt_def] >> first_x_assum irule >> simp[]) >>
  gvs[FLOOKUP_DEF]
QED
