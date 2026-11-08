Theory bodyPtrBytestringBuiltinsOpcodeAggregates
Ancestors bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeValues bodyPtrBytestringBuiltinsOpcodeState
          exprLowering context list

(* Callback contracts are local to the elements actually compiled. Supported
   source lists can discharge these contracts element by element. *)
Theorem no_extcode_make_tuple:
  !cfn ce es.
  (!e s. MEM e es /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce (expr_type e) e s))) ==>
  !buf off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_make_tuple cfn ce es buf off s))
Proof
  ntac 2 gen_tac >> Induct >>
  simp[compile_make_tuple_def, no_extcode_fresh_ops] >> rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_unwrap_value, no_extcode_store_memory])
QED

Theorem no_extcode_make_array_elems:
  !cfn ce es.
  (!e s. MEM e es /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce (expr_type e) e s))) ==>
  !et sz lw buf idx s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_make_array_elems cfn ce es et sz lw buf idx s))
Proof
  ntac 2 gen_tac >> Induct >>
  simp[compile_make_array_elems_def, no_extcode_fresh_ops] >> rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_unwrap_value, no_extcode_store_memory])
QED

Theorem no_extcode_make_array:
  !cfn ce es.
  (!e s. MEM e es /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce (expr_type e) e s))) ==>
  !et sz lw buf s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_make_array cfn ce es et sz lw buf s))
Proof
  rpt strip_tac >> simp[compile_make_array_def] >>
  irule no_extcode_ignore_bind >>
  simp[no_extcode_make_array_elems] >>
  Cases_on `lw` >> simp[no_extcode_emit_void, no_extcode_fresh_ops]
QED

Theorem no_extcode_multi_exprs:
  !cfn ce es.
  (!e s. MEM e es /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce (expr_type e) e s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_multi_exprs cfn ce es s))
Proof
  ntac 2 gen_tac >> Induct >>
  simp[compile_multi_exprs_def, no_extcode_fresh_ops] >> rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_lower_value, no_extcode_fresh_ops])
QED

Theorem no_extcode_struct_lit:
  !cfn ce ty fields.
  (!name e s. MEM (name,e) fields /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce (expr_type e) e s))) ==>
  !buf off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_struct_lit cfn ce ty fields buf off s))
Proof
  ntac 3 gen_tac >> Induct >>
  simp[compile_struct_lit_def, no_extcode_fresh_ops] >>
  gen_tac >> PairCases_on `h` >> simp[compile_struct_lit_def] >> rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_unwrap_value, no_extcode_store_memory]) >>
  metis_tac[]
QED

Theorem no_extcode_store_abi_tuple:
  !ce buf off vals s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_store_abi_tuple ce buf off vals s))
Proof
  ntac 2 gen_tac >> Induct_on `vals` >>
  simp[compile_store_abi_tuple_def, no_extcode_fresh_ops] >>
  rpt gen_tac >> PairCases_on `h` >> simp[compile_store_abi_tuple_def] >>
  rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_copy_memory])
QED
