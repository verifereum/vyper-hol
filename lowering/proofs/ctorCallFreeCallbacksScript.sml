(* Callback boundaries: hypotheses are restricted to the actual children. *)
Theory ctorCallFreeCallbacks
Ancestors
  list pair compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  ctorCallFreeRules supportedExprTraverse ctorCallFreeValues

Theorem every_state_insts_lower_value:
  (!st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ty e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ty e st)))
Proof
  strip_tac >> simp[lower_value_def, every_state_insts_bind]
QED

Theorem every_state_insts_lower_value_with_loc:
  (!st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ty e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value_with_loc cfn cenv ty e st)))
Proof
  strip_tac >> simp[lower_value_with_loc_def, every_state_insts_bind,
    every_state_insts_return]
QED

Theorem outcomes_free_multi_exprs:
  !es s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_multi_exprs f ce es s)))
Proof
  Induct_on `es` >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_multi_exprs_def, every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return,
      every_state_insts_lower_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value]),
    gen_tac, strip_tac, irule every_state_insts_bind, conj_tac,
    first_assum irule]) >> simp[]
QED

Theorem opcode_every_multi_exprs:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_multi_exprs cfn cenv es st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_multi_exprs >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_make_tuple:
  !es tys buf off s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_tuple f ce es tys buf off s)))
Proof
  Induct_on `es` >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `tys` >> simp[compile_make_tuple_def, every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, first_assum irule]) >>
  simp[]
QED

Theorem opcode_every_make_tuple:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce src dst dty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) ==>
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !tys buf off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_make_tuple cfn cenv es tys buf off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_make_tuple >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_make_array_elems:
  !es ety sz lw buf idx s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_array_elems f ce es ety sz lw buf idx s)))
Proof
  Induct_on `es` >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_make_array_elems_def, every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, first_assum irule]) >>
  simp[]
QED

Theorem opcode_every_make_array_elems:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce src dst dty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) ==>
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !ety sz len_word buf idx st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_make_array_elems cfn cenv es ety sz len_word buf idx st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_make_array_elems >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_make_array:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_array f ce es ety sz lw buf s)))
Proof
  strip_tac >> simp[compile_make_array_def] >>
  irule every_state_insts_ignore_bind >> conj_tac
  >- (Cases_on `lw` >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
          opcode_every_emit_inst]) >>
  rpt strip_tac >> simp[outcomes_free_make_array_elems]
QED

Theorem opcode_every_make_array:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce src dst dty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) /\
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  (!e ty st. MEM e es ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_make_array cfn cenv es ety sz len_word buf st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_make_array >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_struct_lit:
  !fields buf off s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  (!nm e ty st. MEM (nm,e) fields /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_struct_lit f ce ty fields buf off s)))
Proof
  Induct_on `fields` >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_struct_lit_def, every_state_insts_return] >>
  rename1 `compile_struct_lit _ _ _ (fld::_)` >> PairCases_on `fld` >>
  simp[compile_struct_lit_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, first_assum irule]) >>
  metis_tac[]
QED

Theorem opcode_every_struct_lit:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce src dst dty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) ==>
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !fields cfn cenv.
  (!name e ty st. MEM (name,e) fields ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !sty buf off st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_struct_lit cfn cenv sty fields buf off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_struct_lit >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> qpat_x_assum `!name e ty st. MEM _ fields ==> _` drule >>
  disch_then irule >> simp[]
QED

Theorem outcomes_free_concat:
  !es infos dp off s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; MCOPY] ==> P opc) /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_concat f ce es dp infos off s)))
Proof
  Induct_on `es` >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_concat_def, every_state_insts_return] >>
  Cases_on `infos` >> simp[compile_concat_def, every_state_insts_return] >>
  rename1 `compile_concat _ _ (e::es) _ (info::rest)` >> PairCases_on `info` >>
  simp[compile_concat_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst,
      every_state_insts_lower_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC, first_assum irule]) >>
  simp[]
QED

Theorem opcode_every_concat:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !data_op infos off_op st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_concat cfn cenv es data_op infos off_op st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_concat >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_attribute:
  P ADD /\
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (cfn cenv ty base_e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_attribute cfn cenv ret_ty ty base_e field_name s)))
Proof
  strip_tac >> qpat_x_assum `EVERY _ (state_insts s)` mp_tac >>
  qid_spec_tac `s` >> simp[compile_attribute_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, every_state_insts_return])])
QED

Theorem opcode_every_attribute:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (cfn cenv ty base_e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_attribute cfn cenv ret_ty ty base_e field_name st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_attribute >> simp[]
QED

Theorem outcomes_free_acc:
  P BALANCE /\ P EXTCODEHASH /\ P EXTCODESIZE /\ P GT /\ P INVALID /\
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv (BaseT AddressT) addr_e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_acc cfn cenv addr_e accessor st)))
Proof
  strip_tac >> Cases_on `accessor` >> simp[compile_acc_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[opcode_every_emit_op, opcode_every_emit_inst, SND]
QED

Theorem opcode_every_acc:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (lower_value cfn cenv (BaseT AddressT) addr_e st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_acc cfn cenv addr_e accessor st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_acc >> simp[]
QED

Theorem every_state_insts_subscript:
  (!ety st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ety idx_e st)))) /\
  (!st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ty base_e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_snapshot_vv cenv T vv st)))) /\
  (!v st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_keccak256_key v F st)))) /\
  (!v k st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_mapping_subscript v k st)))) /\
  (!v off st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_tuple_subscript v off st)))) /\
  (!v idx dyn count ws sz signed loc st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_array_subscript v idx dyn count ws sz signed
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st)))) ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_subscript cfn cenv ret_ty ty base_e idx_e st)))
Proof
  strip_tac >> simp[compile_subscript_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (rw[] >> gvs[every_state_insts_return]) >>
  gen_tac >> reverse (Cases_on `place_type cenv base_e`) >> simp[]
  >- (rename1 `ValPT bty` >> Cases_on `bty` >> simp[] >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return])])) >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return])])
QED

Theorem every_state_insts_get_target_ptr:
  (!e ety st. ~supported_expr_exists R e /\ ~supported_expr_exists root2 e ==>
    EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ety e st)))) /\
  (!v st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_keccak256_key v F st)))) /\
  (!v k st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_mapping_subscript v k st)))) /\
  (!ops st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (emit_op ADD ops st)))) /\
  (!v idx dyn count ws sz signed loc st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_array_subscript v idx dyn count ws sz signed
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st)))) ==>
  !target. ~supported_target_exists R target /\ ~supported_target_exists root2 target ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_get_target_ptr cfn cenv target st)))
Proof
  strip_tac >>
  `( !e:expr. T) /\ (!target. ~supported_target_exists R target /\
     ~supported_target_exists root2 target ==> !st. EVERY P (state_insts st) ==>
     EVERY P (state_insts (SND (compile_get_target_ptr cfn cenv target st))))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[supported_expr_exists_def, compile_get_target_ptr_def] >> rpt conj_tac >> rpt gen_tac
  >- (rpt CASE_TAC >> simp[every_state_insts_return])
  >- (rpt CASE_TAC >> simp[every_state_insts_return])
  >- (ntac 2 strip_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
      gen_tac >> Cases_on `SND (SND result)` >> simp[] >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return, every_state_insts_bind]),
        CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> simp[])]) >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return])])) >>
  strip_tac >> gen_tac >> strip_tac >> gvs[] >> ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> simp[every_state_insts_bind, every_state_insts_return]
QED

Theorem outcomes_free_mapping_subscript:
  P ALLOCA /\ P MSTORE /\ P ADD /\ P SHA3 /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_mapping_subscript b k s)))
Proof
  strip_tac >> simp[compile_mapping_subscript_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        outcomes_free_alloc_buffer]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

(* Strict subscript prerequisites; allocation remains a cross-family premise. *)
Theorem opcode_every_mapping_subscript:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!sz st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_alloc_buffer sz st)))) ==>
  !base key st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_mapping_subscript base key st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_mapping_subscript >> simp[]
QED

Theorem outcomes_free_keccak256_key:
  P ALLOCA /\ P MSTORE /\ P ADD /\ P MLOAD /\ P SHA3 /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_keccak256_key k flag s)))
Proof
  strip_tac >> Cases_on `flag` >> simp[compile_keccak256_key_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        outcomes_free_alloc_buffer]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

Theorem opcode_every_keccak256_key:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_keccak256_key v F st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_keccak256_key >> simp[]
QED

Theorem outcomes_free_tuple_subscript:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_subscript b n s)))
Proof
  simp[compile_tuple_subscript_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst]
QED

Theorem opcode_every_tuple_subscript:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !base off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_subscript base off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_tuple_subscript >> simp[]
QED

Theorem outcomes_free_array_subscript:
  (!b st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (loader b st)))) /\
  P SLT /\ P LT /\ P ISZERO /\ P OR /\ P ASSERT /\ P ADD /\ P MUL /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_array_subscript b i d n ws sz sg loader s)))
Proof
  strip_tac >> Cases_on `d` >> Cases_on `sg` >>
  simp[compile_array_subscript_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        every_state_insts_return]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

Theorem opcode_every_array_subscript:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !base idx dyn count ws sz signed loader.
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (loader v st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_array_subscript base idx dyn count ws sz signed loader st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_array_subscript >> simp[]
QED
