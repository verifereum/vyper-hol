Theory deployOutcomesFreeStmtControl
Ancestors
  ctorCallFreeRules
  stmtLowering compileEnv emitHelper venomInst
  loweringShapeDefs

Theorem outcomes_free_return_unlock:
  (!key transient view s.
     EVERY P (state_insts s) ==>
     EVERY P (state_insts
       (SND (compile_nonreentrant_unlock key transient view s)))) ==>
  !cenv s. EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (compile_return_unlock cenv s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `cenv.ce_nonreentrant` >>
  rename1 `cenv.ce_nonreentrant = (nr, rest)` >>
  PairCases_on `rest` >>
  simp[compile_return_unlock_def] >>
  Cases_on `nr` >> simp[every_state_insts_return]
QED

Theorem outcomes_free_internal_return_from_env:
  P MLOAD /\
  (!env s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_return_unlock env s)))) /\
  (!env value rpc count ty sty elems buf s.
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_internal_return env value rpc count ty sty elems buf s)))) ==>
  !env ty sty value rpc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_internal_return_from_env env ty sty value rpc s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `env.ce_return_buf` >>
  simp[compile_internal_return_from_env_def] >-
   (rpt (FIRST [irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
                irule ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
                gen_tac, disch_tac]) >>
    simp[every_state_insts_return, comp_bind_def, comp_return_def]) >>
  rename1 `env.ce_return_buf = SOME loc` >> Cases_on `loc` >>
  simp[] >>
  rpt (FIRST [irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
              irule ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
      every_state_insts_return, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, emit_def, fresh_var_def, fresh_id_def] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[outcomes_free_state_insts, mk_inst_def]
QED
