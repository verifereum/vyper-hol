Theory bodyPtrBytestringBuiltinsOpcodeLocals
Ancestors bodyPtrBytestringBuiltinsOpcodeState stmtLowering
Libs BasicProvers

Theorem no_extcode_declare_local:
  !ce id ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (declare_local ce id ty s))
Proof
  rpt strip_tac >> simp[declare_local_def] >> IF_CASES_TAC >>
  simp[no_extcode_fresh_ops] >> irule no_extcode_bind >>
  simp[no_extcode_fresh_ops]
QED

Theorem no_extcode_declare_stmt_local:
  !ce stmt s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (declare_stmt_local ce stmt s))
Proof
  rpt gen_tac >> Cases_on `stmt` >>
  simp[declare_stmt_local_def, no_extcode_declare_local, no_extcode_fresh_ops]
QED

Theorem no_extcode_emit_local_alloca:
  !ce id s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (emit_local_alloca ce id s))
Proof
  rpt strip_tac >> simp[emit_local_alloca_def] >>
  TOP_CASE_TAC >> simp[no_extcode_fresh_ops] >>
  TOP_CASE_TAC >> simp[no_extcode_fresh_ops] >>
  TOP_CASE_TAC >> simp[no_extcode_fresh_ops, no_extcode_emit_inst]
QED
