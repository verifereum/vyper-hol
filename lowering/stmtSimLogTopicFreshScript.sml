(* Operational absence preservation for topic-generated variable names. *)
Theory stmtSimLogTopicFresh
Ancestors
  stmtSimLogTopics freshWrites exprLoweringProps emitHelper emitHelperProps
  context stmtLowering compileEnv venomExecSemantics venomInst venomState
  words list rich_list arithmetic finite_map ASCIInumbers

Theorem log_topic_outputs[local]:
  compile_encode_log_topic op flag sa = (out,sb) /\ sb.cs_next_var <= nv ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; SHA3] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
      i.inst_outputs) (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_topic_step_var[local]:
  MEM inst.inst_opcode [ADD; MLOAD; SHA3] /\
  step_inst_base inst s = OK t /\ ~MEM x inst.inst_outputs ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  cheat
QED

Theorem log_topic_code_var[local]:
  !code s t x. EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; SHA3] /\
    ~MEM x i.inst_outputs) code /\ run_inst_seq code s = OK t ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  cheat
QED

Theorem log_topics_counters[local]:
  !raw sa ops sb. compile_log_topic_ops raw sa = (ops,sb) ==>
    sa.cs_next_var <= sb.cs_next_var
Proof
  cheat
QED

Theorem log_topics_outputs[local]:
  !raw sa ops sb nv. compile_log_topic_ops raw sa = (ops,sb) /\
    sb.cs_next_var <= nv ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; SHA3] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
      i.inst_outputs) (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_topics_fresh:
  compile_log_topic_ops raw sm = (ops,sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  cheat
QED
