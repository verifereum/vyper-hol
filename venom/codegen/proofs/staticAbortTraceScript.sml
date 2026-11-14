(* Concrete, finite assembly traces for static-abort progress. *)
Theory staticAbortTrace
Ancestors
  asmSem asmIR stackOpSim

Definition static_abort_safe_at_def:
  static_abort_safe_at prog s <=>
    s.as_pc < LENGTH prog /\
    case EL s.as_pc prog of
      AsmOp name => IS_SOME (evm_opcode_byte name) /\
        ~MEM name ["CALL"; "CALLCODE"; "STATICCALL"; "DELEGATECALL";
                   "CREATE"; "CREATE2"; "SELFDESTRUCT"]
    | AsmDataHeader _ => F
    | AsmDataItem _ => F
    | AsmDataLabel _ => F
    | _ => T
End

Definition static_abort_trace_def:
  static_abort_trace lo o2pc prog n s <=>
    !k mid. k < n /\ asm_steps lo o2pc prog k s = AsmOK mid ==>
      mid.as_requests = s.as_requests /\ static_abort_safe_at prog mid
End

Definition static_abort_normal_def:
  static_abort_normal lo o2pc prog n s t <=>
    asm_steps lo o2pc prog n s = AsmOK t /\
    t.as_requests = s.as_requests /\
    static_abort_trace lo o2pc prog n s
End

Definition static_abort_exception_def:
  static_abort_exception lo o2pc prog n s t <=>
    (asm_steps lo o2pc prog n s = AsmFault t \/
     asm_steps lo o2pc prog n s = AsmRevert t) /\
    t.as_requests = s.as_requests /\ t.as_returndata = [] /\
    static_abort_trace lo o2pc prog n s
End

Theorem static_abort_trace_zero[simp]:
  static_abort_trace lo o2pc prog 0 s
Proof
  simp[static_abort_trace_def]
QED

Theorem static_abort_normal_zero[simp]:
  static_abort_normal lo o2pc prog 0 s t <=> t = s
Proof
  simp[static_abort_normal_def] >> metis_tac[]
QED

Theorem static_abort_trace_append:
  static_abort_normal lo o2pc prog a s t /\
  static_abort_trace lo o2pc prog b t ==>
  static_abort_trace lo o2pc prog (a + b) s
Proof
  pure_rewrite_tac[static_abort_normal_def] >> strip_tac >>
  fs[static_abort_trace_def] >>
  map_every qx_gen_tac [`k`, `mid`] >> strip_tac >>
  Cases_on `k < a`
  >- metis_tac[] >>
  `k = a + (k - a) /\ k - a < b` by decide_tac >>
  `asm_steps lo o2pc prog (k - a) t = AsmOK mid` by
    metis_tac[asm_steps_add_ok] >>
  metis_tac[]
QED

Theorem static_abort_normal_append:
  static_abort_normal lo o2pc prog a s t /\
  static_abort_normal lo o2pc prog b t u ==>
  static_abort_normal lo o2pc prog (a + b) s u
Proof
  strip_tac >>
  `static_abort_trace lo o2pc prog (a + b) s` by
    (irule static_abort_trace_append >>
     qexists `t` >> gvs[static_abort_normal_def]) >>
  gvs[static_abort_normal_def] >>
  metis_tac[asm_steps_add_ok]
QED

Theorem static_abort_exception_append:
  static_abort_normal lo o2pc prog a s t /\
  static_abort_exception lo o2pc prog b t u ==>
  static_abort_exception lo o2pc prog (a + b) s u
Proof
  strip_tac >>
  `static_abort_trace lo o2pc prog (a + b) s` by
    (irule static_abort_trace_append >>
     qexists `t` >> gvs[static_abort_exception_def]) >>
  gvs[static_abort_normal_def, static_abort_exception_def] >>
  metis_tac[asm_steps_add_ok]
QED

Theorem static_abort_exception_bound_mono:
  n <= bound /\ bound <= bound' /\
  static_abort_exception lo o2pc prog n s t ==>
  n <= bound' /\ static_abort_exception lo o2pc prog n s t
Proof
  simp[]
QED
