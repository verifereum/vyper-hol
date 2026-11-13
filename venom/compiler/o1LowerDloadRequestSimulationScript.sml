(* Root lifting for the abort-sensitive LowerDload runner.
 * The conditional interface deliberately needs no endpoint or exec clauses:
 * final assembly supplies its universally closed run predicate.
 *)
Theory o1LowerDloadRequestSimulation
Ancestors
  o1LowerDloadRequestRunner o1LowerDloadRequestControl
  o1LowerDloadRequestExec o1LowerDloadRequestEndpoints
  o1LowerDloadRequestForward o1ContractLowerDloadSim o1RequestContract
  o1PassContract o1LowerDloadJointRelation o1LowerDloadRootEntry
  ptrDiscipline passSimulationDefs venomExecSemantics venomState
  venomExecProps venomInst o1LowerDloadSourceEntry list

(* Retain the literal run conjunct, including every guard and quantifier.
 * Close its schematic environment so the premise can be specialized at
 * each root execution independently.
 *)
val ldRequestRun = List.nth (strip_conj (snd (dest_imp
  (concl ld_request_runner_induction))), 2);
val ldRequestRunClosed = list_mk_forall (free_vars ldRequestRun, ldRequestRun);

Theorem lower_dload_stage_abort_rq_conditional:
  ^ldRequestRunClosed ==>
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    ctx_abort_rq D C C' vs vs
Proof
  disch_then (assume_tac o SIMP_RULE bool_ss []) >>
  rpt strip_tac >> simp[ctx_abort_rq_def] >> rpt strip_tac >>
  `terminates (Abort a t)` by simp[terminates_def] >>
  drule_all lower_dload_stage_root_entry >> strip_tac >>
  `opaque_use_ok fn` by metis_tac[ld_ctx_shape_lookup_opaque] >>
  `fn.fn_name = name` by
    (qpat_assum `lookup_function name C.ctx_functions = SOME fn`
       (mp_tac o REWRITE_RULE [lookup_function_def]) >>
     disch_then (mp_tac o MATCH_MP FIND_P) >> simp[]) >>
  `terminates (run_blocks fuel C fn s0)` by metis_tac[] >>
  first_assum (drule_at (Pat `ld_joint_boundary`) o SIMP_RULE bool_ss []) >>
  simp[] >>
  disch_then (drule_at (Pat `terminates (run_blocks _ _ _ _)`)) >>
  simp[] >> disch_then (drule_all_then strip_assume_tac) >>
  gvs[ld_request_result_rel_abort] >>
  qexists_tac `m` >> simp[] >>
  irule LIST_REL_imp_request_prefix_rel >> simp[]
QED

(* All recursive clauses retain the strengthened terminal observation. *)
val ldRequestConclusion = snd (dest_imp (concl ld_request_runner_induction));

Theorem ld_request_runner_simulation:
  ^ldRequestConclusion
Proof
  MATCH_MP_TAC ld_request_runner_induction >>
  conj_tac >- MATCH_ACCEPT_TAC ld_request_runner_step_clause >>
  conj_tac
  >- (MATCH_MP_TAC ld_request_runner_exec_conditional >> conj_tac
      >- (rpt strip_tac >> drule_all ld_runner_abort_endpoint_requests >>
          metis_tac[]) >>
      MATCH_ACCEPT_TAC ld_runner_forward_endpoint_requests) >>
  MATCH_ACCEPT_TAC ld_request_runner_run_clause
QED
