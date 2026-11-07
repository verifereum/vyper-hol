Theory dftGasFromListCalleeSeed
Ancestors
  dftGasFromListRestore gasOracleReplay dftGasOracleDefs
  contextCodegenRel venomExecSemantics venomInst venomState

Theorem restored_callee_entry:
  active_inst fn inst s /\
  ev_reachable orc vs0 ctx p d fn inst (s with vs_gas_readings := gs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs u /\ active_inst callee i u ==>
  ev_reachable orc vs0 ctx ((d,inst.inst_id)::p) (SUC d) callee i
    (u with vs_gas_readings := gs)
Proof
  strip_tac >>
  `setup_callee callee args (s with vs_gas_readings := gs) =
    SOME (cs with vs_gas_readings := gs)` by simp[gas_setup_callee] >>
  drule enters_block_restore >> disch_then (qspec_then `gs` assume_tac) >>
  metis_tac[ev_reachable_callee, active_inst_restore, gas_eval_operands]
QED
