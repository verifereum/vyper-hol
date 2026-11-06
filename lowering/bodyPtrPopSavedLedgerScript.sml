Theory bodyPtrPopSavedLedger
Ancestors bodyPtrPopSavedExecution bodyPtrPopTraceReplay
  bodyPtrPopTraceRuntime bodyPtrPopTraceChecks

(* This joins two bounded observations only. The ghost is defined by the
   exact prefix recurrence, whose runtime successors are checked separately.
   No inst_seq_ptr, supported entry, body_inv, or universal operand judgment
   is asserted. The call-free example mutates the enclosing array's length;
   it does not test calls, reentrancy, aliasing writes, or arbitrary indices. *)
Theorem pop_saved_actual_taint_header:
  ?s. run_inst_seq (SND pop_saved_header).cs_current_insts
      pop_saved_runtime = OK s /\
    eval_operand (FST pop_saved_header) s = SOME 2w /\
    sload 0w s = 1w /\ sload 8w s = 2w /\
    pop_region_taint_ok
      (s.vs_accounts s.vs_call_ctx.cc_address).storage 8
      (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2))
      (pop_trace_taint 37).t_stor /\
    dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage 0
      (ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
        (Dynamic 2)) (Dynamic 2)) 8 0
Proof
  mp_tac pop_saved_next_header >> simp[pop_trace_storage_final]
QED
