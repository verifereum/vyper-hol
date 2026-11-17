Theory concretizeLayoutDelegateBoundary
Ancestors concretizeLayoutReaderContext concretizeLayoutExternalRequests
  frameRelocationEnvironment venomExecSemantics ptrDiscipline

(* DELEGATECALL snapshots agree outside the final task's dead masks. *)
Theorem concretize_delegate_clean_snapshots:
  concretize_supplement D tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = DELEGATECALL /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) ==>
  accounts_agree_except D s.vs_accounts t.vs_accounts /\
  transient_agree_except D s.vs_transient t.vs_transient
Proof
  strip_tac >>
  fs[concretizeLayoutSupplementTheory.concretize_supplement_def] >>
  conj_tac >>
  gvs[accounts_agree_except_def, transient_agree_except_def,
      storage_agree_except_def, key_taint_def, word_agree_except_def,
      pred_setTheory.SUBSET_DEF] >>
  rpt gen_tac >> Cases_on `a = s.vs_call_ctx.cc_address` >> gvs[] >> metis_tac[]
QED
