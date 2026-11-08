Theory bodyPtrBytestringBuiltinsOpcodeMemory
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState context exprLowering
          compileEnv emitHelper

Theorem no_extcode_copy_memory:
  !dst src n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_copy_memory dst src n s))
Proof
  rpt gen_tac >> Cases_on `n` >>
  simp[compile_copy_memory_def, no_extcode_fresh_ops, no_extcode_emit_void]
QED

Theorem no_extcode_copy_memory_dynamic:
  !dst src len s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_copy_memory_dynamic dst src len s))
Proof
  simp[compile_copy_memory_dynamic_def, no_extcode_emit_void]
QED

Theorem no_extcode_with_byte_offset:
  !base off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_with_byte_offset base off s))
Proof
  rpt gen_tac >> Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, no_extcode_fresh_ops, no_extcode_emit_op]
QED

Theorem no_extcode_bytestring_copy_len:
  !src s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_bytestring_copy_len src s))
Proof
  rpt strip_tac >> simp[compile_bytestring_copy_len_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_fresh_ops])
QED

Theorem no_extcode_store_bytestring:
  !src dst s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_store_bytestring src dst s))
Proof
  rpt strip_tac >> simp[compile_store_bytestring_def] >>
  irule no_extcode_bind >>
  simp[no_extcode_bytestring_copy_len, no_extcode_emit_void]
QED

Theorem no_extcode_typed_copy:
  (!cenv dst dt src st s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_store_memory_typed cenv dst dt src st s))) /\
  (!cenv dst src dts sts doff soff s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s))) /\
  (!cenv dst dt src st n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_copy_sarray_typed cenv dst dt src st n s))) /\
  (!cenv dst dt cap src st s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_copy_dynarray_typed cenv dst dt cap src st s))) /\
  (!cenv dst src dfs sfs doff soff s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  conj_tac >- suspend "dispatch" >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[] >> simp[Once compile_store_memory_typed_def, no_extcode_fresh_ops] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY (pairarg_tac >> gvs[]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    gvs[no_extcode_emit_inst, no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_new_block, no_extcode_fresh_ops, no_extcode_copy_memory,
      no_extcode_copy_memory_dynamic, no_extcode_with_byte_offset]) >>
  simp[no_extcode_copy_memory]
QED

Resume no_extcode_typed_copy[dispatch]:
  rpt strip_tac >> simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC >- (irule no_extcode_bind >>
    simp[no_extcode_emit_op, no_extcode_emit_void]) >>
  IF_CASES_TAC >- simp[no_extcode_store_bytestring] >>
  IF_CASES_TAC >- simp[no_extcode_emit_void] >>
  Cases_on `dt` >> simp[no_extcode_copy_memory] >>
  Cases_on `st` >> gvs[no_extcode_copy_memory] >>
  BasicProvers.TOP_CASE_TAC >> gvs[no_extcode_copy_memory] >>
  BasicProvers.TOP_CASE_TAC >> gvs[no_extcode_copy_memory]
QED

Finalise no_extcode_typed_copy

Theorem no_extcode_store_memory:
  !cenv src dst dt st s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_store_memory cenv src dst dt st s))
Proof
  rpt strip_tac >> simp[compile_store_memory_def] >>
  rpt (IF_CASES_TAC >>
    simp[no_extcode_emit_void, no_extcode_store_bytestring,
      cj 1 no_extcode_typed_copy, no_extcode_copy_memory])
QED

Theorem no_extcode_ifexp_arm:
  !cenv res_ty arm_ty vv s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_ifexp_arm cenv res_ty arm_ty vv s))
Proof
  rpt strip_tac >> simp[compile_ifexp_arm_def] >>
  IF_CASES_TAC >- simp[no_extcode_unwrap_value] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_alloc_buffer, no_extcode_unwrap_value,
      no_extcode_store_memory, no_extcode_fresh_ops])
QED
