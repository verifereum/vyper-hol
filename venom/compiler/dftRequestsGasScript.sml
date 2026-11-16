(*
 * DFT's request companion, under the input oracle dft_ctx_sim_gas chooses:
 * the same chosen input state gives the simulation, the abort companion
 * (ctx_abort_rq) and the lowered invariant.  DFT may run an ASSERT before
 * a CALL it does not depend on, so the output's requests at an abort are
 * a prefix of the input's, not the whole list.
 *)
Theory dftRequestsGas
Ancestors
  dftGasRequestContract dftGasRequestLift dftGasRequestSwap dftGasRequestPartner
  dftGasRequestSchedule dftGasRequestRel
  dftContractGas o1DftStageSsa o1RequestContract o1PassContract o1PassLift unitMemInv
  dftDefs venomPassSchedule venomExecSemantics venomState list

(* The selector supplies replay for this literal filling; no new input
   reading list is selected at the stage boundary. *)
Theorem dft_stage_replay_rq_gas:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\ dead_wf D /\
  o1_run_state_ok vs' /\
  (!fuel. gas_res_rel (run_context fuel C (vs' with vs_gas_readings := rds))
                     (ev_context orc fuel C vs')) /\
  (!fuel. gas_res_rel (run_context fuel C' vs') (ev_context orc fuel C' vs')) /\
  (!p d fn inst t. ev_reachable orc vs' C p d fn inst t ==>
     ?ws. raw_reachable (vs' with vs_gas_readings := rds) C fn inst
               (t with vs_gas_readings := ws)) /\
  (!fn inst t. raw_reachable vs' C' fn inst t ==>
     ?p d. ev_reachable orc vs' C' p d fn inst
               (t with vs_gas_readings := vs'.vs_gas_readings)) ==>
  ctx_sim_fuel I D C C' (vs' with vs_gas_readings := rds) vs' /\
  ctx_abort_rq D C C' (vs' with vs_gas_readings := rds) vs' /\
  (o1_lowered_inv C (vs' with vs_gas_readings := rds) ==>
   o1_lowered_inv C' vs')
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  `ctx_labels_bound C vs'.vs_labels` by
    (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
  irule dft_ctx_replay_rq_gas >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule dft_ev_context_sim_rq >> simp[]) >>
  qexists_tac `orc` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem dft_ctx_sim_rq_gas:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ dead_wf D /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim_fuel I D C C' vs vs' /\
       ctx_abort_rq D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  strip_tac >>
  irule dft_ctx_sim_rq_gas_conditional >>
  simp[] >> rpt strip_tac >>
  irule dft_ev_context_sim_rq >> simp[]
QED
