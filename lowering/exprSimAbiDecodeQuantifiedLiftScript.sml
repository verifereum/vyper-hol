Theory exprSimAbiDecodeQuantifiedLift
Ancestors
  exprSimAbiDecodeOutcomeAllocation exprSimAbiDecodeObserverReject
  exprSimAbiDecodePathReconstruct exprSimAbiDecodePathLift
  abiEncoderVarTransport exprSimAbiGasBridge abiEncoderObserver
  abiDecoderVarExtend abiDecoderLoop fragExec venomExecSemantics venomState
  venomInst relation

Theorem abi_decode_observer_success_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t) /\
  (t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut sb /\
  abi_decoder_vars_extend extras s s' ==>
  ?u u'. stop_view u = stop_view t /\
    abi_decoder_vars_extend extras u u' /\
    local_prefix ctx fn (frag_observer_cut sb) s' u' /\
    abi_decode_sim ctx fn s' u'
Proof
  strip_tac >>
  `?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[] >>
     conj_tac >- (qexists_tac `fuel` >> simp[]) >>
     simp[stop_view_def, halt_state_def]) >>
  drule_all abi_encoder_local_prefix_extend >> strip_tac >>
  `local_prefix ctx fn (frag_observer_cut sb) s' t'` by
    (qpat_assum `abi_decoder_vars_extend extras s s'`
       (mp_then Any strip_assume_tac abi_encoder_vars_extend_control) >>
     qpat_assum `local_prefix _ _ _ s' t'`
       (mp_then Any mp_tac frag_observer_prefix_transfer) >>
     disch_then (qspecl_then [`sa`, `sb`, `fn`, `id`] mp_tac) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`u`, `t'`] >> simp[] >>
  metis_tac[local_prefix_sim]
QED

Theorem abi_decode_observer_rtc_transfer:
  !s t. RTC (abi_observer_step ctx (frag_observer sa sb fn id)
                    (frag_observer_cut sb)) s t ==>
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb ==>
  RTC (abi_observer_step ctx fn (frag_observer_cut sb)) s t
Proof
  ho_match_mp_tac RTC_INDUCT >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  rename1 `abi_observer_step _ _ _ s middle` >>
  irule (cj 2 RTC_RULES) >> qexists_tac `middle` >>
  conj_tac
  >- (irule frag_observer_step_transfer >> metis_tac[]) >>
  drule_all frag_observer_region_closed >>
  simp[observer_region_closed_def] >> strip_tac >>
  `(middle.vs_current_bb,middle.vs_inst_idx) IN frag_observer_region sa sb` by
    (qpat_x_assum `!id' ctx' s t. _`
       (qspecl_then [`id`, `ctx`, `s`, `middle`] mp_tac) >> simp[]) >>
  qpat_x_assum `cs_extends _ _ /\ _ ==> _` mp_tac >> simp[]
QED

Theorem abi_decode_observer_reject_transfer_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = Abort Revert_abort v /\
  abi_decoder_vars_extend extras s s' ==>
  ?v' fuel'. abi_decoder_vars_extend extras v v' /\
    run_from fuel' ctx fn s' = Abort Revert_abort v'
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all abi_decode_frag_observer_reject_lift >> strip_tac >>
  `RTC (abi_observer_step ctx fn (frag_observer_cut sb)) s' u'` by
    (irule abi_decode_observer_rtc_transfer >>
     qexistsl_tac [`id`, `sa`] >> simp[] >>
     qpat_assum `abi_decoder_vars_extend extras s s'`
       (mp_then Any strip_assume_tac abi_encoder_vars_extend_control) >>
     drule frag_observer_start_region >> gvs[] >> metis_tac[]) >>
  drule_all frag_observer_entry_code_agrees >>
  disch_then (qspec_then `id` mp_tac) >>
  simp[frag_entry_code_agrees_def] >> strip_tac >>
  qpat_x_assum `!lbl idx bb inst. _`
    (qspecl_then [`u'.vs_current_bb`, `u'.vs_inst_idx`, `bb`, `inst`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `v'` >> simp[] >>
  irule abi_decode_observer_rtc_reject >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem abi_decode_observer_continuation_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!fuel r. run_from fuel ctx (frag_observer sa sb fn id) t = r /\
    (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx (frag_observer sa sb fn id) s = r) /\
  abi_decoder_vars_extend extras s s' ==>
  ?u u'. stop_view u = stop_view t /\
    abi_decoder_vars_extend extras u u' /\
    local_prefix ctx fn (frag_observer_cut sb) s' u' /\
    abi_decode_sim ctx fn s' u'
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `run_from 0 ctx (frag_observer sa sb fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction] >>
     qexists_tac `id` >> simp[]) >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule abi_decode_observer_success_extend >>
  simp[frag_observer_cut_def] >>
  qexistsl_tac [`fuel`, `id`, `s`, `sa`] >> simp[] >>
  drule frag_observer_start_region >> simp[] >> metis_tac[]
QED

(* One run function at a time: the caller keeps fn universally quantified.
   Success consumes a freshly reconstructed continuation, never the pruned one. *)
Theorem abi_decode_observer_outcome_extend:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  abi_decoder_vars_extend extras s s' /\
  (!t u u'. post t /\ stop_view u = stop_view t /\
    abi_decoder_vars_extend extras u u' /\
    local_prefix ctx fn (frag_observer_cut sb) s' u' ==> post' u') /\
  ((?t. post t /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      !fuel r. run_from fuel ctx (frag_observer sa sb fn id) t = r /\
        (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx (frag_observer sa sb fn id) s = r) \/
   (reject /\ ?fuel v.
      run_from fuel ctx (frag_observer sa sb fn id) s = Abort Revert_abort v)) ==>
  (?t'. post' t' /\ abi_decode_sim ctx fn s' t') \/
  (reject /\ ?fuel v'. run_from fuel ctx fn s' = Abort Revert_abort v')
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `(?t. _) \/ _` strip_assume_tac
  >- (drule_all abi_decode_observer_continuation_extend >> strip_tac >>
      disj1_tac >> qexists_tac `u'` >> simp[] >>
      first_x_assum irule >> simp[] >> qexistsl_tac [`t`, `u`] >> simp[]) >>
  drule_all abi_decode_observer_reject_transfer_extend >> strip_tac >>
  disj2_tac >> simp[] >> metis_tac[]
QED
