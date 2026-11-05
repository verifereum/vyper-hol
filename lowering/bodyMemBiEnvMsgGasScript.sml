(* Counted environment GAS: allocation history at the actual landing cursor. *)
Theory bodyMemBiEnvMsgGas
Ancestors
  msgGasSim allocaHistory compileEnv venomInst venomState list arithmetic

Theorem compile_msg_gas_history:
  compile_env_var MsgGas sa = (Var out,sb) /\ fn_has_code sa sb func /\
  alloca_history func s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  alloca_history func
    (update_var out w
      (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                 vs_inst_idx := LENGTH sb.cs_current_insts|>))
Proof
  strip_tac >> drule_all msg_gas_placement >> strip_tac >>
  gvs[alloca_history_def, update_var_def] >>
  rpt strip_tac >>
  Cases_on `k < LENGTH sa.cs_current_insts`
  >- metis_tac[] >>
  `k = LENGTH sa.cs_current_insts` by decide_tac >>
  gvs[mk_inst_def]
QED
