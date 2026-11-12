Theory deployOutcomesFreeStmtValues
Ancestors
  deployOutcomesFreeLowering stmtLowering compileEnv

Theorem outcomes_free_compile_load_tuple_elements:
  P ADD /\ P MLOAD ==>
  !tys cenv base offset s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_load_tuple_elements cenv base tys offset s)))
Proof
  strip_tac >> Induct_on `tys` >>
  simp[compile_load_tuple_elements_def, outcomes_free_return] >>
  rpt gen_tac >> strip_tac >>
  irule outcomes_free_bind >> reverse conj_tac
  >- simp[outcomes_free_emit_ops] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule outcomes_free_bind >> reverse conj_tac
  >- simp[outcomes_free_emit_ops] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule outcomes_free_bind >>
  simp[outcomes_free_return]
QED

Theorem outcomes_free_compile_tuple_load_all:
  P ADD /\
  (!op word s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_load_memory op word s)))) ==>
  !tys cenv base offset s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_load_all cenv base tys offset s)))
Proof
  strip_tac >> Induct_on `tys` >>
  simp[compile_tuple_load_all_def, outcomes_free_return] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule outcomes_free_bind >> reverse conj_tac
  >- simp[outcomes_free_emit_ops] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule outcomes_free_bind >> reverse conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule outcomes_free_bind >>
  simp[outcomes_free_return]
QED

Theorem outcomes_free_compile_store_at_loc:
  P MSTORE /\ P SSTORE /\ P TSTORE /\ P INVALID /\
  (!imm dst value s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_imm_store_word imm dst value s)))) ==>
  !imm dst value loc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_at_loc imm dst value loc s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `loc`
  >- simp[compile_store_at_loc_def, outcomes_free_emit_ops] >>
  Cases_on `x` >> simp[compile_store_at_loc_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_compile_mcopy_guard:
  P INVALID /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (supported s)))) ==>
  !cenv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_mcopy_guard cenv supported s)))
Proof
  rpt strip_tac >> simp[compile_mcopy_guard_def] >>
  IF_CASES_TAC >> simp[outcomes_free_emit_ops]
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
  >- (Cases_on `ret` >> simp[outcomes_free_emit_ops] >>
      Cases_on `elems = []` >> simp[outcomes_free_emit_ops] >>
      irule outcomes_free_bind >> reverse conj_tac
      >- simp[outcomes_free_compile_load_tuple_elements] >>
      simp[outcomes_free_emit_ops]) >>
  Cases_on `buf` >> simp[outcomes_free_emit_ops] >>
  Cases_on `ret` >> simp[outcomes_free_emit_ops] >>
  irule outcomes_free_ignore_bind >>
  simp[outcomes_free_emit_ops]
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
  irule outcomes_free_ignore_bind >> simp[] >> conj_tac
  >- (Cases_on `lock` >> simp[outcomes_free_return]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  Cases_on `ret` >> simp[outcomes_free_emit_ops] >>
  Cases_on `raw` >> simp[]
  >- (irule outcomes_free_bind >> reverse conj_tac
      >- simp[outcomes_free_emit_ops] >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      irule outcomes_free_bind >> reverse conj_tac
      >- simp[outcomes_free_emit_ops] >>
      simp[outcomes_free_emit_ops]) >>
  Cases_on `prim` >> simp[] >>
  irule outcomes_free_bind >> reverse conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  simp[comp_bind_def, comp_return_def] >> BETA_TAC
  >- (irule outcomes_free_ignore_bind >> simp[outcomes_free_emit_ops]) >>
  pairarg_tac >> gvs[] >>
  irule (cj 3 outcomes_free_emit_ops) >> simp[] >>
  metis_tac[pairTheory.SND]
QED
