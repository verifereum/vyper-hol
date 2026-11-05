(* Stores preserve names above the generated output frontier. *)
Theory stmtSimLogStoreFresh
Ancestors
  stmtSimLogStoreContinue stmtSimLogTopics stmtSimLogDataRun
  freshWrites exprLoweringProps emitHelper emitHelperProps exprSimBufferStore context stmtLowering compileEnv
  venomExecSemantics venomInst venomState words list rich_list arithmetic finite_map ASCIInumbers

Theorem log_store_scalar_outputs[local]:
  supported_scalar_type ty /\ compile_store_memory ce src dst ty ty sa = ((),sb) /\
  sb.cs_next_var <= nv ==>
  EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
    i.inst_outputs) (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_store_step_var[local]:
  MEM inst.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY] /\
  step_inst_base inst s = OK t /\ ~MEM x inst.inst_outputs ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  cheat
QED

Theorem log_store_code_var[local]:
  !code s t x. EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY] /\
    ~MEM x i.inst_outputs) code /\ run_inst_seq code s = OK t ==>
  FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  cheat
QED

Theorem log_store_code_fresh[local]:
  EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY] /\
    EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv) i.inst_outputs) code /\
  run_inst_seq code s = OK t /\ nv <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==> fresh_vars_wrt limit_st t
Proof
  cheat
QED

Theorem log_store_data_outputs[local]:
  !xs buf off sa sb nv. EVERY (supported_scalar_type o SND) xs /\
    compile_log_store_data ce xs buf off sa = ((),sb) /\ sb.cs_next_var <= nv ==>
    EVERY (\i. MEM i.inst_opcode [ADD; AND; MLOAD; MSTORE; MCOPY] /\
      EVERY (\x. ?n. x = STRING #"%" (toString n) /\ n < nv)
        i.inst_outputs) (emitted_insts sa sb)
Proof
  cheat
QED

Theorem log_store_data_fresh:
  EVERY (supported_scalar_type o SND) xs /\
  compile_log_store_data ce xs buf off sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  cheat
QED
