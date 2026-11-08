Theory bodyPtrBytestringBuiltinsOpcodeTuples
Ancestors bodyPtrBytestringBuiltinsOpcodeTargets
          bodyPtrBytestringBuiltinsOpcodeStmtMemory
          bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState
          stmtLowering supportedStmts vyperAST list
Libs BasicProvers

Theorem no_extcode_tuple_store_all:
  !tys tops bindings ce targets vals s.
    EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                         | TupleTarget _ => F) targets /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_tuple_store_all ce tys targets vals s))
Proof
  Induct >> rpt gen_tac >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, no_extcode_fresh_ops] >>
  Cases_on `h'` >> simp[] >> strip_tac >>
  simp[compile_tuple_store_all_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_fresh_ops, no_extcode_store_at_loc, no_extcode_assign_value,
      no_extcode_emit_void]) >>
  metis_tac[no_extcode_target_supported]
QED

Theorem no_extcode_tuple_unpack:
  !tops bindings ce ty stage targets src s.
    EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                         | TupleTarget _ => F) targets /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_tuple_unpack ce ty stage targets src s))
Proof
  rpt strip_tac >> simp[compile_tuple_unpack_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_inst, no_extcode_emit_void, no_extcode_alloc_buffer,
      no_extcode_tuple_load_all, no_extcode_fresh_ops]) >>
  metis_tac[no_extcode_tuple_store_all]
QED
