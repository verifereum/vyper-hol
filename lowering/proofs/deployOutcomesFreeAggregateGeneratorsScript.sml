Theory deployOutcomesFreeAggregateGenerators
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeGenerators exprLowering context emitHelper compileEnv
  list pair venomInst vyperAST deployOutcomesFreeTyping
  supportedExprTraverse vyperTypeSystem

Theorem outcomes_free_make_tuple:
  !es buf off s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_tuple f ce es buf off s)))
Proof
  Induct_on `es` >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_make_tuple_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, first_assum irule]) >>
  simp[]
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
  simp[compile_make_array_elems_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, first_assum irule]) >>
  simp[]
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
  irule outcomes_free_ignore_bind >> conj_tac
  >- (Cases_on `lw` >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
      simp[outcomes_free_return, outcomes_free_emit_ops]) >>
  rpt strip_tac >> simp[outcomes_free_make_array_elems]
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
  simp[compile_multi_exprs_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_lower_value_opcodes]),
    gen_tac, strip_tac, irule outcomes_free_bind, conj_tac,
    first_assum irule]) >> simp[]
QED

Theorem outcomes_free_store_abi_tuple:
  !args buf off s. P ADD /\ P MSTORE /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_abi_tuple ce buf off args s)))
Proof
  Induct_on `args` >> rpt strip_tac >>
  simp[compile_store_abi_tuple_def, outcomes_free_return] >>
  PairCases_on `h` >> simp[compile_store_abi_tuple_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_copy_memory]),
    gen_tac, strip_tac, irule outcomes_free_bind, irule outcomes_free_ignore_bind,
    conj_tac, IF_CASES_TAC, first_assum irule])
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
  simp[compile_struct_lit_def, outcomes_free_return] >>
  PairCases_on `h` >> simp[compile_struct_lit_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, first_assum irule]) >>
  metis_tac[]
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
  simp[compile_concat_def, outcomes_free_return] >>
  Cases_on `infos` >> simp[compile_concat_def, outcomes_free_return] >>
  PairCases_on `h'` >> simp[compile_concat_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_lower_value_opcodes]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    irule outcomes_free_ignore_bind, conj_tac, IF_CASES_TAC, first_assum irule]) >>
  simp[]
QED

Theorem outcomes_free_acc:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; BALANCE; EXTCODESIZE; EXTCODEHASH; GT] ==> P opc) /\
  (!ty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_acc f ce e item s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `item` >> simp[compile_acc_def, outcomes_free_emit_ops] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_emit_ops]),
    gen_tac, strip_tac]) >>
  `EVERY (\i. P i.inst_opcode)
     (state_insts (SND (lower_value f ce (BaseT AddressT) e s)))` by
    (irule outcomes_free_lower_value_opcodes >> simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  gvs[outcomes_free_emit_ops] >>
  rpt (pairarg_tac >> gvs[outcomes_free_emit_ops]) >>
  metis_tac[outcomes_free_emit_ops, SND]
QED

(* Materialization is discharged by the ABI generator publication at the join. *)
Theorem outcomes_free_abi_encode_args:
  !es s.
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  (!e ty st. MEM e es /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  (!ty vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_materialize_vv ce ty vv st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_args f ce es s)))
Proof
  Induct_on `es` >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_abi_encode_args_def, outcomes_free_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value]),
    gen_tac, strip_tac, irule outcomes_free_bind,
    conj_tac, IF_CASES_TAC, first_assum irule]) >> simp[]
QED

Theorem outcomes_free_aggregate_typed_callbacks:
  (!e ty st. well_typed_expr env e /\ ~supported_expr_exists root e /\
     Q st ==> Q (SND (f ce ty e st))) /\
  well_typed_exprs env es /\ ~supported_exprs_exists root es ==>
  (!e ty st. MEM e es /\ Q st ==> Q (SND (f ce ty e st)))
Proof
  simp[outcomes_free_typed_exprs_every, supported_exprs_exists_every,
    EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem outcomes_free_aggregate_typed:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  (!e ty st. well_typed_expr env e /\ ~supported_expr_exists root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  well_typed_exprs env es /\ ~supported_exprs_exists root es /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_tuple f ce es buf off s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_make_array f ce es ety sz lw buf s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_concat f ce es buf infos offptr s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_multi_exprs f ce es s)))
Proof
  strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >> rpt conj_tac >>
  FIRST [irule outcomes_free_make_tuple, irule outcomes_free_make_array,
    irule outcomes_free_concat, irule outcomes_free_multi_exprs] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  fs[outcomes_free_typed_exprs_every, supported_exprs_exists_every,
     EXISTS_MEM, EVERY_MEM] >> metis_tac[]
QED

Theorem outcomes_free_struct_lit_typed:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] ==> P opc) /\
  (!e ty st. well_typed_expr env e /\ ~supported_expr_exists root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\kv. well_typed_expr env (SND kv) /\
    ~supported_expr_exists root (SND kv)) fields /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_struct_lit f ce ty fields buf off s)))
Proof
  strip_tac >> irule outcomes_free_struct_lit >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `EVERY _ fields` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `(nm,e)` mp_tac) >> simp[] >>
  strip_tac >> first_x_assum irule >> simp[]
QED

Theorem outcomes_free_acc_typed:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; BALANCE; EXTCODESIZE; EXTCODEHASH; GT] ==> P opc) /\
  (!e ty st. well_typed_expr env e /\ ~supported_expr_exists root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  well_typed_expr env e /\ ~supported_expr_exists root e /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_acc f ce e item s)))
Proof
  strip_tac >> irule outcomes_free_acc >> simp[]
QED

Theorem outcomes_free_abi_encode_args_typed:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  (!e ty st. well_typed_expr env e /\ ~supported_expr_exists root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  (!ty vv st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_materialize_vv ce ty vv st)))) /\
  EVERY (\e. well_typed_expr env e /\ ~supported_expr_exists root e) es /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_args f ce es s)))
Proof
  strip_tac >> irule outcomes_free_abi_encode_args >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `EVERY _ es` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >>
  strip_tac >> first_x_assum irule >> simp[]
QED

Theorem outcomes_free_multi_exprs_typed:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  (!e ty st. well_typed_expr env e /\ ~supported_expr_exists root e /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce ty e st)))) /\
  EVERY (\e. well_typed_expr env e /\ ~supported_expr_exists root e) es /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_multi_exprs f ce es s)))
Proof
  strip_tac >> irule outcomes_free_multi_exprs >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `EVERY _ es` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >>
  strip_tac >> first_x_assum irule >> simp[]
QED
