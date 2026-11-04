Theory cseHistoryProps
Ancestors passSharedProps venomExecSemantics venomState

(* Local copy transport only: the persistence premise must be established
   for the particular later execution occurrence by a separate argument. *)
Theorem cse_assign_historical_transport:
  !fuel ctx inst src dst s t u v.
    inst.inst_outputs = [dst] /\
    eval_operand src s = SOME v /\
    step_inst fuel ctx (mk_assign_inst inst src) s = OK t /\
    lookup_var dst u = lookup_var dst t ==>
    eval_operand (Var dst) u = eval_operand src s
Proof
  rpt strip_tac >>
  drule_all mk_assign_inst_correct >> strip_tac >> gvs[] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED
