Theory bodyPtrBytestringBuiltinsCreatePrimitiveAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsCallStagingAllocationTrace
          bodyPtrBytestringBuiltinsOperatorAllocationTrace builtinCreate builtinSystem

Theorem compile_msg_data_to_memory_allocation_trace[simp]:
  !s. allocation_trace s (SND (compile_msg_data_to_memory s))
Proof
  rpt gen_tac >> simp[compile_msg_data_to_memory_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_raw_call_outbuf_allocation_trace[simp]:
  !n s. allocation_trace s (SND (compile_raw_call_outbuf n s))
Proof
  rpt gen_tac >> simp[compile_raw_call_outbuf_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_raw_call_finish_allocation_trace[simp]:
  !addr ptr len gas value ct n rev out data s.
    allocation_trace s (SND (compile_raw_call_finish addr ptr len gas value ct n rev out data s))
Proof
  rpt gen_tac >> Cases_on `ct` >> simp[compile_raw_call_finish_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_check_create_result_allocation_trace[simp]:
  !result rev s. allocation_trace s (SND (compile_check_create_result result rev s))
Proof
  rpt gen_tac >> simp[compile_check_create_result_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >>
       simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_create_dispatch_allocation_trace[simp]:
  !ptr len value salt rev s.
    allocation_trace s (SND (compile_create_dispatch ptr len value salt rev s))
Proof
  rpt gen_tac >> Cases_on `salt` >> simp[compile_create_dispatch_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_create_proxy_buf_allocation_trace[simp]:
  !addr s. allocation_trace s (SND (compile_create_proxy_buf addr s))
Proof
  rpt gen_tac >> simp[compile_create_proxy_buf_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_create_copy_allocation_trace[simp]:
  !addr value salt rev s.
    allocation_trace s (SND (compile_create_copy addr value salt rev s))
Proof
  rpt gen_tac >> Cases_on `salt` >> simp[compile_create_copy_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED

Theorem compile_create_blueprint_check_allocation_trace[simp]:
  !addr off s. allocation_trace s (SND (compile_create_blueprint_check addr off s))
Proof
  rpt gen_tac >> simp[compile_create_blueprint_check_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_create_blueprint_append_allocation_trace[simp]:
  !addr value salt off sz ptr len rev s.
    allocation_trace s (SND (compile_create_blueprint_append addr value salt off sz ptr len rev s))
Proof
  rpt gen_tac >> Cases_on `salt` >> simp[compile_create_blueprint_append_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind, IF_CASES_TAC] >> simp[])
QED
