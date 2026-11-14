(* Local replay boundaries for the DFT code_end invariant.
   These use the oracle and reading list already chosen by dft_ctx_sim_gas;
   neither boundary chooses an independent oracle. *)
Theory o1CodeEndDftBoundary
Ancestors
  dftGasInvResidualTrace dftGasOracleToList gasOracleReplay
  contextRawReachable

(* A crossed, successfully replayed prefix preserves every operand of the
   observation, without restricting the observation to memory opcodes.
   In particular the observation may be LowerDload's ADD. *)
Theorem dft_replay_prefix_operands:
  !pre s t.
    EVERY (\x. inst_wf x /\ ~is_pseudo x.inst_opcode /\
      ~is_terminator x.inst_opcode /\ x.inst_opcode <> INVOKE /\
      ~dft_must_order x obs) pre /\
    inv_ev_trace orc p d fuel ctx pre s t ==>
    !op. MEM op obs.inst_operands ==> eval_operand op t = eval_operand op s
Proof
  Induct >> simp[inv_ev_trace_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all inv_crossing_operand_frame >> metis_tac[]
QED

(* The prefix-reachability clause exported by gas_oracle_to_list retains
   operand values at its SAME W. This applies even to visits in a run that
   later errors or never terminates. *)
Theorem dft_replay_operand_at_readings:
  (!p d fn inst t. ev_reachable orc initial ctx p d fn inst t ==>
    ?ws. raw_reachable (initial with vs_gas_readings := readings) ctx fn inst
      (t with vs_gas_readings := ws)) /\
  ev_reachable orc initial ctx p d fn inst t /\
  eval_operand op t = value ==>
  ?u. raw_reachable (initial with vs_gas_readings := readings) ctx fn inst u /\
    eval_operand op u = value
Proof
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED
