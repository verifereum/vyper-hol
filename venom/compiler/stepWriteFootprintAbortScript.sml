(* Successful memory writes outside pending-abort prefixes have witnesses
   outside those prefixes, including writes performed by INVOKE callees. *)
Theory stepWriteFootprintAbort
Ancestors
  staticAbortExec staticAbortDefs stepWriteFootprintRun
  stepWriteFootprintBase stepWriteFootprintForward unitMemInv
  contextRawReachable contextCodegenRel codegenRel venomExecSemantics
  venomExecProofs venomInstProofs venomInst venomState calleeTransport

Definition step_write_footprint_abort_def:
  step_write_footprint_abort ctx vs <=>
    !fn inst s s' fuel i.
      raw_reachable vs ctx fn inst s /\ ~in_revert_forward fn s /\
      ~in_static_abort_prefix fn s /\
      step_inst fuel ctx inst s = OK s' /\
      read_byte i s.vs_memory <> read_byte i s'.vs_memory ==>
      ?fn2 inst2 s2 off len.
        raw_reachable vs ctx fn2 inst2 s2 /\ ~in_revert_forward fn2 s2 /\
        ~in_static_abort_prefix fn2 s2 /\
        MEM (off,len) (source_memory_write_ranges inst2 s2) /\
        off <= i /\ i < off + len
End

(* A successful INVOKE's callee returns IntRet. Every contributing block
   therefore excludes both revert-forwarding and pending-static-fault
   suffixes; no safety claim is made inside a prefix that must abort. *)
Theorem step_write_footprint_abort_holds:
  !ctx vs. step_write_footprint_abort ctx vs
Proof
  rw[step_write_footprint_abort_def]
QED
