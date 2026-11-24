(* The Send arity check admits the member IH at every invariant source state. *)
Theory entryCreateSendWordGuard
Ancestors
  exprSimSend exprSimHypsDefs vyperState

Theorem send_guarded_member_ih:
  !ce cx env ann has_gas args dflt es Child.
    expr_body_pre ce cx env (Call ann (Send has_gas) args dflt) es /\
    (!st x t.
      type_check (LENGTH args = (if has_gas then 3 else 2)) "Send args" st =
        (INL x,t) ==>
      !e ee. MEM e args /\ expr_body_pre ce cx env e ee ==> Child e ee) ==>
    !e ee. MEM e args /\ expr_sim_inv ce cx env ee ==> Child e ee
Proof
  rpt gen_tac >> strip_tac >>
  drule send_pre_types >> strip_tac >>
  `!e ee. MEM e args /\ expr_body_pre ce cx env e ee ==> Child e ee` by
    (qpat_assum `!st x t. type_check _ _ st = (INL x,t) ==> _`
       (qspec_then `es` mp_tac) >>
     simp[type_check_def,check_def,assert_def]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  metis_tac[expr_body_pre_send_arg]
QED
