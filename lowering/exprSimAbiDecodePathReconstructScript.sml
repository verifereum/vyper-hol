Theory exprSimAbiDecodePathReconstruct
Ancestors
  abiEncoderObserver abiDecoderLoop fragExec venomExecSemantics venomInst
  relation

Theorem abi_decode_observer_rtc_prefix:
  !s t. RTC (abi_observer_step ctx fn cut) s t ==>
    ~t.vs_halted /\ (t.vs_current_bb,t.vs_inst_idx) = cut ==>
    local_prefix ctx fn cut s t
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
  irule (cj 2 local_prefix_rules) >> metis_tac[]
QED

Theorem abi_decode_observer_rtc_sim:
  !s t. RTC (abi_observer_step ctx fn cut) s t ==>
    abi_decode_sim ctx fn s t
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- simp[abi_decode_sim_refl] >>
  drule abi_observer_step_sim >> strip_tac >>
  drule_all abi_decode_sim_trans >> simp[]
QED

Theorem abi_decode_observer_rtc_reject:
  RTC (abi_observer_step ctx fn cut) s u /\ ~u.vs_halted /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\
  step_inst_base inst u = Abort Revert_abort v ==>
  ?fuel. run_from fuel ctx fn s = Abort Revert_abort v
Proof
  strip_tac >>
  `run_from 0 ctx fn u = Abort Revert_abort v` by
    simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  drule abi_decode_observer_rtc_sim >>
  rewrite_tac[abi_decode_sim_def] >>
  disch_then (qspecl_then [`0`, `Abort Revert_abort v`] mp_tac) >> simp[]
QED
