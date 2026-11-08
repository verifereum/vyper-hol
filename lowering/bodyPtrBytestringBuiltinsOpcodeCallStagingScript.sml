Theory bodyPtrBytestringBuiltinsOpcodeCallStaging
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeState exprLowering emitHelper

Theorem no_extcode_pair:
  !p k. compiler_no_extcode (SND p) /\
    (!v t. compiler_no_extcode t ==> compiler_no_extcode (SND (k v t))) ==>
    compiler_no_extcode (SND (UNCURRY k p))
Proof
  rpt gen_tac >> PairCases_on `p` >> simp[]
QED

Theorem no_extcode_fresh_vars:
  !n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (fresh_vars n s))
Proof
  Induct >> simp[fresh_vars_def, no_extcode_fresh_ops] >> rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_fresh_ops])
QED

Theorem no_extcode_emit_multi_op:
  !opc args n s. opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (emit_multi_op opc args n s))
Proof
  rpt strip_tac >> simp[emit_multi_op_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_fresh_ops, no_extcode_fresh_vars, no_extcode_emit_inst])
QED

Theorem no_extcode_multi_vvs:
  !cfn ce es.
  (!e s. MEM e es /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce (expr_type e) e s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_multi_vvs cfn ce es s))
Proof
  ntac 2 gen_tac >> Induct >> simp[compile_multi_vvs_def, no_extcode_fresh_ops] >>
  rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_fresh_ops])
QED

Theorem no_extcode_store_multi_results:
  !buf vs off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (store_multi_results buf vs off s))
Proof
  gen_tac >> Induct >> simp[store_multi_results_def, no_extcode_fresh_ops] >>
  rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_extcall_store_values:
  !ce vs buf off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_extcall_store_values ce vs buf off s))
Proof
  gen_tac >> Induct >> simp[compile_extcall_store_values_def, no_extcode_fresh_ops] >>
  gen_tac >> PairCases_on `h` >> simp[compile_extcall_store_values_def] >>
  rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_unwrap_value, no_extcode_store_bytestring])
QED

Theorem no_extcode_stage_intcall_args:
  !ce vs flags tys s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_stage_intcall_args ce vs flags tys s))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt strip_tac >>
  simp[Once compile_stage_intcall_args_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_unwrap_value, no_extcode_alloc_buffer, no_extcode_store_memory,
         no_extcode_copy_memory, no_extcode_store_bytestring])
QED
