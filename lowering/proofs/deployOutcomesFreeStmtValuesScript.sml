Theory deployOutcomesFreeStmtValues
Ancestors
  ctorCallFreeRules
  stmtLowering compileEnv

Theorem outcomes_free_compile_load_tuple_elements:
  P ADD /\ P MLOAD ==>
  !tys cenv base offset s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_load_tuple_elements cenv base tys offset s)))
Proof
  strip_tac >> Induct_on `tys` >>
  simp[compile_load_tuple_elements_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
  >- simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
  >- simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  simp[every_state_insts_return]
QED

Theorem outcomes_free_compile_internal_return:
  P RET /\ P ADD /\ P MLOAD /\
  (!cenv value buf ty src s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory cenv value buf ty src s)))) ==>
  !cenv ret pc count ty src elems buf s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND
        (compile_internal_return cenv ret pc count ty src elems buf s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_internal_return_def] >>
  IF_CASES_TAC >> simp[]
  >- (Cases_on `ret` >> simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst] >>
      Cases_on `elems = []` >> simp[opcode_every_emit_op, opcode_every_emit_void,
          opcode_every_emit_inst] >>
      irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
      >- simp[outcomes_free_compile_load_tuple_elements] >>
      simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]) >>
  Cases_on `buf` >> simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  Cases_on `ret` >> simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >>
  simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_external_return:
  P STOP /\ P MLOAD /\ P ADD /\ P MSTORE /\ P RETURN /\
  (!nkey trans view s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_nonreentrant_unlock nkey trans view s)))) /\
  (!size s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_alloc_buffer size s)))) /\
  (!buf value info s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_to_buf buf value info s)))) ==>
  !ret prim raw info size lock key trans view s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND
        (compile_external_return ret prim raw info size lock key trans view s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_external_return_def] >>
  irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> simp[] >> conj_tac
  >- (Cases_on `lock` >> simp[every_state_insts_return]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  Cases_on `ret` >> simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  Cases_on `raw` >> simp[]
  >- (irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
      >- simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
      >- simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
      simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]) >>
  Cases_on `prim` >> simp[] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  simp[comp_bind_def, comp_return_def] >> BETA_TAC
  >- (irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]) >>
  pairarg_tac >> gvs[] >>
  irule opcode_every_emit_inst >> simp[] >>
  metis_tac[pairTheory.SND]
QED
