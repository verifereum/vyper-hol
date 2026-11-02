(* TOP-LEVEL: run_call_supply for actual OWHILE execution.
 *)
Theory vyperRunSupply
Ancestors
  vyperExecutionSupply vyperOpcodeSupply vyperHandlerSupply
  vfmExecution vfmContext While
Libs
  proofAuditLib

(* run_call uses only step, not transaction fee/finalization accounting. *)
Theorem run_call_supply:
  supply_state budget initial /\
  run_call initial = SOME (result,post) ==>
  supply_state budget post
Proof
  simp[run_call_def] >> strip_tac >>
  qspecl_then
    [`\rs. supply_state budget (SND rs)`,
     `\(r,s). ISL r /\ LENGTH s.contexts >= LENGTH initial.contexts`,
     `vfmExecution$step o SND`, `(INL (),initial)`]
    mp_tac (GEN_ALL OWHILE_INV_IND) >>
  impl_tac
  >- (simp[] >> rw[] >> irule supply_action_snd >>
      simp[supply_action_step]) >>
  disch_then (qspec_then `(result,post)` mp_tac) >> simp[]
QED

val () = proofAuditLib.check_theory "vyperRunSupply";
