(* Abort-sensitive observation for the LowerDload mutual runner.
 * The existing successful-step and return packets are reused verbatim.
 * Only the terminal observation is strengthened; no old relation changes.
 *)
Theory o1LowerDloadRequestRunner
Ancestors
  o1LowerDloadRunner ptrDiscipline venomExecSemantics venomState list
  passSimulationDefs

Definition ld_request_result_rel_def:
  ld_request_result_rel D r r' <=>
    dead_result_rel D r r' /\
    (case (r,r') of
       (Abort a s, Abort b t) =>
         LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
     | _ => T)
End

Theorem ld_request_result_rel_projection:
  ld_request_result_rel D r r' ==> dead_result_rel D r r'
Proof
  simp[ld_request_result_rel_def]
QED

Theorem ld_request_result_rel_halt:
  ld_request_result_rel D (Halt s) r' <=>
    dead_result_rel D (Halt s) r'
Proof
  Cases_on `r'` >> simp[ld_request_result_rel_def]
QED

Theorem ld_request_result_rel_abort:
  ld_request_result_rel D (Abort a s) r' <=>
    ?b t. r' = Abort b t /\ (a = Revert_abort ==> b = Revert_abort) /\
      LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
Proof
  Cases_on `r'` >> simp[ld_request_result_rel_def, dead_result_rel_def]
QED

Theorem ld_request_result_rel_nonterminal:
  (~ld_request_result_rel D (OK s) r') /\
  (~ld_request_result_rel D (IntRet ir s) r') /\
  (~ld_request_result_rel D (Error e) r')
Proof
  Cases_on `r'` >> simp[ld_request_result_rel_def, dead_result_rel_def]
QED

(* Reuse the checked runner templates, rather than maintain a second copy
 * of their continuation witnesses. The consequent of the old induction
 * interface contains, in order, the step, exec and run predicate applied
 * to their universally quantified arguments. Substitution affects only
 * dead_result_rel; hence the OK/IntRet packets and recursive guards remain
 * literally those of the existing runner.
 *)
val ldRequestStrengthen = Term.subst
  [``dead_result_rel`` |-> ``ld_request_result_rel``];
val ldRequestPredicates = map
  (ldRequestStrengthen o fst o strip_comb o snd o strip_forall)
  (strip_conj (snd (dest_imp (concl ld_runner_conditional_induction))));
val (ldRequestIndVars,ldRequestIndBody) = strip_forall (concl run_defs_ind);
val ldRequestInd = Term.subst (ListPair.map (fn (v,t) => v |-> t)
  (ldRequestIndVars,ldRequestPredicates)) ldRequestIndBody;
val ldRequestPacket = ldRequestStrengthen
  (fst (strip_comb (fst (dest_imp (concl ld_runner_packet_terminates)))));

(* Export all three clause premises. Consumers extract their exact clauses
 * from this theorem, so there is only one strengthened logical interface.
 *)
Theorem ld_request_runner_induction:
  ^ldRequestInd
Proof
  MATCH_ACCEPT_TAC run_defs_ind
QED

Theorem ld_request_runner_packet_terminates:
  ^ldRequestPacket stk PG fn a U HP ts A0 r r' ==> terminates r'
Proof
  Cases_on `r` >> simp[terminates_def] >> rpt strip_tac >> gvs[terminates_def]
QED

(* Terminal-slot probes: these cover the runner result packet itself.
 * INVOKE's terminal slots use the same observation by construction above.
 *)
Theorem ld_request_runner_packet_abort:
  ^ldRequestPacket stk PG fn a U HP ts A0 (Abort ab s) r' <=>
    ?t. r' = Abort ab t /\
      LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
Proof
  Cases_on `r'` >> simp[ld_request_result_rel_abort] >> metis_tac[]
QED

Theorem ld_request_runner_packet_halt:
  ^ldRequestPacket stk PG fn a U HP ts A0 (Halt s) r' <=>
    ?t. r' = Halt t /\ dead_result_rel D (Halt s) r'
Proof
  simp[ld_request_result_rel_halt]
QED
