Theory bodyFullAbiDecodeCutPath
Ancestors
  exprSimAbiDecodePathReconstruct abiEncoderObserver abiDecoderLoop
  venomExecSemantics relation
Libs
  bodyFullAbiDecodeCutPathLib

(* A reachable cursor need not yet be the outer cut.  At that cut the same
   finite trace is a local_prefix, without taking the STOP instruction. *)
Theorem abi_decode_cut_prefix_at_end:
  RTC (abi_observer_step ctx obs cut) u w /\
  ~w.vs_halted /\ (w.vs_current_bb,w.vs_inst_idx) = cut ==>
  local_prefix ctx obs cut u w
Proof
  metis_tac[abi_decode_observer_rtc_prefix]
QED

(* A completed continuation can be prefixed by a trace, including a setup
   local_prefix whose own cut is the temporary ready cursor.  The continuation
   fuel need not work at the beginning of the prefix. *)
Theorem abi_decode_cut_prefix_run:
  (RTC (abi_observer_step ctx obs cut) u w \/ local_prefix ctx obs cut u w) /\
  run_from fuel ctx obs w = r /\ (!e. r <> Error e) ==>
  ?k. run_from k ctx obs u = r
Proof
  strip_tac >>
  `abi_decode_sim ctx obs u w` by
    metis_tac[abi_decode_observer_rtc_sim, local_prefix_sim] >>
  pop_assum (mp_tac o REWRITE_RULE[abi_decode_sim_def]) >>
  disch_then (qspecl_then [`fuel`, `r`] mp_tac) >> simp[]
QED

Theorem abi_decode_cut_prefix_bind:
  RTC (abi_observer_step ctx obs cut) u w /\
  (^(bodyFullAbiDecodeCutPathLib.shadow_result)) ctx obs cut L entry w cursor r ==>
  (^(bodyFullAbiDecodeCutPathLib.shadow_result)) ctx obs cut L entry u cursor r
Proof
  simp_tac bool_ss [BETA_THM] >> strip_tac
  >- (disj1_tac >> metis_tac[RTC_TRANS]) >>
  disj2_tac >>
  rename1 `run_from fuel ctx obs w = Abort Revert_abort rejected` >>
  `?k. run_from k ctx obs u = Abort Revert_abort rejected` by
    (irule abi_decode_cut_prefix_run >> metis_tac[exec_result_distinct]) >>
  metis_tac[]
QED
