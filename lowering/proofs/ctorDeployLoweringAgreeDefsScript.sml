(* A local copy of deploy_venom_result_rel in its agree form, for the
 * constructor-return piece of deploy_unit_execution_correct: the target's
 * storage and the transient storage agree with the source's up to the dead
 * bytes (accounts_agree, transient_agree at the deployment context), rather
 * than exactly. Replaced by deploy_venom_result_rel once that takes this form.
 *)
Theory ctorDeployLoweringAgreeDefs
Ancestors
  ctorDeployDefs

Definition deploy_venom_result_agree_def:
  deploy_venom_result_agree tops runtime_bc am tx
    (src : (abstract_machine # call_request list) + exception) vres <=>
    case (src, vres) of
      (INL (am', rqs), Halt ss) =>
        ?section.
          ss.vs_returndata = runtime_bc ++ section /\
          immutables_section_rel tops (account_immutables am' tx.target) section /\
          accounts_agree (deploy_evaluation_context tops am tx)
            ((tx.target =+ (am'.accounts tx.target with code := [])) am'.accounts)
            ((tx.target =+ (ss.vs_accounts tx.target with code := []))
               ss.vs_accounts) /\
          transient_agree (deploy_evaluation_context tops am tx)
            am'.tStorage ss.vs_transient /\
          logs_correspond (compiled_event_info tops) (type_env tops)
            tx.target am'.logs ss.vs_logs
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error e), Abort _ _) => T
    | (INR (Error e), Halt _) => unspecified_behaviour_exempt tops e
    | _ => F
End
