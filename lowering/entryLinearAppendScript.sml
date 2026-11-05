(* Linear selector dispatch only appends to the emitted code stream. *)
Theory entryLinearAppend
Ancestors
  moduleLoweringProps moduleLowering fragExec emitHelperProps

Theorem cs_appends_selector_dispatch_linear:
  cs_appends (compile_selector_dispatch_linear sels fallback)
Proof
  simp[compile_selector_dispatch_linear_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cs_appends_prims,
    cs_appends_emit_helpers, compile_selector_checks_appends]),
    gen_tac, irule cs_appends_bind, irule cs_appends_ignore_bind, conj_tac])
QED
