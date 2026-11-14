Theory o1StaticLowerDload
Ancestors
  o1ContractLowerDloadStage

(* LowerDload preserves instruction order. The static guards compare the
   flags of related states; they do not require an initially nonstatic call. *)
Theorem o1_static_stage_lower_dload:
  !C C' vs.
    ctx_pass_stage rpolicy (EL 1 o1_fn_passes) (o1_walk_view rpolicy 1) C C' /\
    o1_pre 1 C C' /\ dead_wf D /\ o1_ctx_shape C /\
    o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
    code_layout_valid vs /\ o1_inv D 1 C vs ==>
    ctx_sim_fuel (pass_fuel (EL 1 o1_fn_passes) C') D C C' vs vs /\
    o1_inv D (SUC 1) C' vs
Proof
  MATCH_ACCEPT_TAC lower_dload_run_contract_static
QED
