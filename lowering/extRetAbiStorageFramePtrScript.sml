(* Storage safety transport for finite memory-only ABI encoder stages. *)
Theory extRetAbiStorageFramePtr
Ancestors bodyPtrDefs ptrDiscipline venomState

Theorem stor_taint_ok_ambient_transport:
  stor_taint_ok cx tn s /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
  sf.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address ==>
  stor_taint_ok cx tnf sf
Proof
  simp[stor_taint_ok_def]
QED
