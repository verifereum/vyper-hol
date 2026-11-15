(*
 * LowerDload's request companion: an aborting run of the input context is
 * matched by an aborting run of the output whose requests are a prefix of
 * the input's up to the dead bytes (ctx_abort_rq), under
 * lower_dload_stage_sim's premises.
 *)
Theory o1LowerDloadRequests
Ancestors
  o1LowerDloadRequestSimulation o1RequestContract o1PassContract ptrDiscipline
  venomPassSchedule venomExecSemantics venomState list

Theorem lower_dload_stage_abort_rq:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    ctx_abort_rq D C C' vs vs
Proof
  MATCH_MP_TAC lower_dload_stage_abort_rq_conditional >>
  rpt gen_tac >> MATCH_ACCEPT_TAC (cj 3 ld_request_runner_simulation)
QED
