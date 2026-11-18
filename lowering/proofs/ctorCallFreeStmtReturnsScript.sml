(* Callback-free return and revert opcode boundaries. *)
Theory ctorCallFreeStmtReturns
Ancestors
  list pair stmtLowering context venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeABI ctorCallFreeABIEncode
  compileEnv emitHelper loweringFunctionOpcodes

Theorem opcode_every_nonreentrant_unlock:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_nonreentrant_unlock key transient view st)))
  )
Proof
  rpt strip_tac >> irule (cj 2 outcomes_free_nonreentrant) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem call_free_nonreentrant_unlock:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_nonreentrant_unlock key transient view st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_nonreentrant_unlock) >> simp[]
QED

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

Theorem opcode_every_load_tuple_elements:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !tys ce base off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_load_tuple_elements ce base tys off st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_compile_load_tuple_elements >> simp[]
QED

Theorem outcomes_free_mcopy_guard:
  P INVALID ==>
  (
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (action st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_mcopy_guard ce action st)))
  )
Proof
  strip_tac >>
  Cases_on `ce.ce_target CapMcopy` >> simp[compile_mcopy_guard_def, opcode_every_emit_inst]
QED

Theorem opcode_every_mcopy_guard:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (action st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_mcopy_guard ce action st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_mcopy_guard >> simp[]
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

Theorem opcode_every_internal_return:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_internal_return ce value pc nrets ty sty elems buf st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_internal_return >>
  simp[UNDISCH opcode_every_store_memory]
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

Theorem opcode_every_external_return:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_external_return value prim raw info maxsz nr key transient view st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_external_return >>
  simp[UNDISCH opcode_every_nonreentrant_unlock, UNDISCH opcode_every_alloc_buffer,
    cj 2 (UNDISCH opcode_every_abi_encode)]
QED

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

Theorem opcode_every_return_unlock:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_return_unlock ce st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_return_unlock >>
  simp[UNDISCH opcode_every_nonreentrant_unlock]
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

Theorem opcode_every_internal_return_from_env:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_internal_return_from_env ce ty sty value pc st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_internal_return_from_env >>
  simp[UNDISCH opcode_every_return_unlock, UNDISCH opcode_every_internal_return]
QED

Theorem outcomes_free_compile_revert_with_reason:
  EVERY P [MSTORE; ADD; MLOAD; NOT; AND; MCOPY; REVERT] /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ce vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (unwrap_value ce vv s)))) ==>
  !ce vv ty sz s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_revert_with_reason ce vv ty sz s)))
Proof
  simp[EVERY_DEF] >> strip_tac >> ntac 4 gen_tac >>
  simp[compile_revert_with_reason_def] >>
  rpt (FIRST [ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
              ho_match_mp_tac ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
              gen_tac]) >>
  metis_tac[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem opcode_every_revert_with_reason:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_revert_with_reason ce msg ty sz st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_revert_with_reason >>
  simp[UNDISCH opcode_every_alloc_buffer, UNDISCH opcode_every_unwrap_value]
QED
