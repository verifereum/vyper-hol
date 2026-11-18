Theory deployOutcomesFreeArgs
Ancestors
  ctorCallFreeRules
  deployOutcomesFreeGenerators abiEncoder moduleLowering context emitHelper
  compileEnv list pair
  ctorCallFreeValues loweringFunctionOpcodes

val outcomes_free_decode_args_fixed =
  SRULE [DISJ_IMP_THM, FORALL_AND_THM] (Q.INST [`P` |-> `\op. op <> CALL /\
    op <> STATICCALL /\ op <> DELEGATECALL /\ op <> CREATE /\ op <> CREATE2 /\
    op <> INVOKE`] outcomes_free_decode_args);

Theorem outcomes_free_register_constructor_args_state:
  !args env off sz s.
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE) (state_insts s) ==>
  EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL /\
    i.inst_opcode <> DELEGATECALL /\ i.inst_opcode <> CREATE /\
    i.inst_opcode <> CREATE2 /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_register_constructor_args env args off sz s)))
Proof
  Induct_on `args` >- simp[compile_register_constructor_args_def, every_state_insts_return] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  Cases_on `FLOOKUP env.ce_vars h0` >>
  simp[compile_register_constructor_args_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (gvs[outcomes_free_alloc_buffer, every_state_insts_return,
      outcomes_free_decode_args_fixed]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac,
    IF_CASES_TAC,
    (qmatch_goalsub_rename_tac `var_location_memory_size loc` >>
      Cases_on `var_location_memory_size loc`)]) >>
  qpat_x_assum `!env off sz s. _` irule >> simp[]
QED
