(* Whitelist removal, deploy leaf: constructor correctness without
   supported_program and constructor_call_free.

   A constructor that makes calls needs the call oracle, as vyper_call_correct
   has it: the source runs load_contract with the outcomes the EVM frame
   recorded, under call_outcomes_ok and with each outcome's storage well
   formed in the deploy context, and its requests must agree with the
   frame's.  deploy_call_result_rel is call_result_rel_at's relation for the
   constructor: the deployed code and immutables section, the frame outcome,
   accounts and transient storage agreeing after the pending deletions (the
   target's code masked, since load_contract leaves the source's account
   without it), the logs and the requests.

   e2e_deploy_correctness_full is admitted; its proof stacks on the deploy
   branch's theorem (the call-free constructor under the premises) and the
   constructor-call pieces. *)
Theory whitelistDeploy
Ancestors
  e2eDeployDefs e2eDefs

Definition deploy_call_result_rel_def:
  deploy_call_result_rel tops runtime_bc am tx es r es' <=>
    ?gobs.
      case load_contract (SOME (MAP SND (call_trace es))) gobs am tx
             [(NONE, tops)] [] of
        INL (am', rqs) =>
          let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
          let accts = process_deletions es'.rollback.toDelete
                        es'.rollback.accounts in
          ?section lgs.
            immutables_section_rel tops (account_immutables am' tx.target)
              section /\
            frame_outcome es r es' NONE (runtime_bc ++ section) lgs /\
            (lookup_account tx.target accts).code = runtime_bc ++ section /\
            accounts_agree cx am'.accounts
              (update_account tx.target
                 (lookup_account tx.target accts with
                    code := (lookup_account tx.target am'.accounts).code)
                 accts) /\
            transient_agree cx am'.tStorage es'.rollback.tStorage /\
            logs_correspond (compiled_event_info tops) (type_env tops)
              tx.target am'.logs lgs /\
            LIST_REL (request_agree cx) rqs (call_requests es)
      | INR (AssertException s) =>
          ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                        (exc = Reverted \/ s = "UNREACHABLE")
      | INR (Error e) =>
          unspecified_behaviour_exempt tops e \/
          ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
      | INR BreakException => F
      | INR ContinueException => F
      | INR (ReturnException _) => F
End

Theorem e2e_deploy_correctness_full:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    call_outcomes_ok am tx (MAP SND (call_trace es)) /\
    EVERY (\co. contract_storage_well_formed (deploy_evaluation_context tops am tx)
                  (initial_state (am with <| accounts := co.co_accounts;
                                             tStorage := co.co_tStorage |>) []))
          (MAP SND (call_trace es)) /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  cheat
QED
