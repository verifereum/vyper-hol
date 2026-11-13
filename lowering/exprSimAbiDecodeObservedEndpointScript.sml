Theory exprSimAbiDecodeObservedEndpoint
Ancestors
  abiEncoderObserver fragExec venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState relation list

Theorem abi_decode_reject_endpoint_aux[local]:
  observer_region_closed ctx fn cut region /\
  (!s bb inst. (s.vs_current_bb,s.vs_inst_idx) IN region /\
    (s.vs_current_bb,s.vs_inst_idx) <> cut /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==> inst.inst_opcode <> INVOKE) /\
  (!s fuel v. (s.vs_current_bb,s.vs_inst_idx) = cut ==>
    run_from fuel ctx fn s <> Abort Revert_abort v) ==>
  !fuel n s bb v.
    (s.vs_current_bb,s.vs_inst_idx) IN region /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx fn s = Abort Revert_abort v ==>
    ?u bb' inst. RTC (abi_observer_step ctx fn cut) s u /\
      (u.vs_current_bb,u.vs_inst_idx) IN region /\
      (u.vs_current_bb,u.vs_inst_idx) <> cut /\ ~u.vs_halted /\
      lookup_block u.vs_current_bb fn.fn_blocks = SOME bb' /\
      get_instruction bb' u.vs_inst_idx = SOME inst /\
      inst.inst_opcode <> INVOKE /\ step_inst_base inst u = Abort Revert_abort v
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  completeInduct_on `fuel` >> completeInduct_on `n` >> rpt strip_tac >>
  `(s.vs_current_bb,s.vs_inst_idx) <> cut` by metis_tac[] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
      simp[Once run_from_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[] >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac
  >- (rename1 `step_inst_base inst s = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary") >>
  qexistsl_tac [`s`, `bb`, `inst`] >> simp[]
QED

Resume abi_decode_reject_endpoint_aux[ordinary]:
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx fn cut s
    (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  `(s.vs_current_bb,SUC s.vs_inst_idx) IN region` by
    (qpat_assum `observer_region_closed _ _ _ _`
       (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- gvs[get_instruction_def]) >>
  disch_then (qspec_then `middle with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >>
  `run_from fuel ctx fn (middle with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort Revert_abort v` by (fs[] >> simp[Once run_from_def]) >>
  disch_then drule_all >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[RTC_RULES]
QED

Resume abi_decode_reject_endpoint_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def] >>
  rename1 `run_blocks (SUC remaining) ctx fn middle = Abort Revert_abort v` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb fn.fn_blocks` >>
  simp[] >>
  rename1 `lookup_block middle.vs_current_bb fn.fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx fn cut s
    (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN region` by
    (qpat_assum `observer_region_closed _ _ _ _`
       (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspec_then
    `entered with vs_inst_idx := phi_prefix_length target.bb_instructions` mp_tac) >>
  simp[] >>
  `run_from remaining ctx fn
    (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
    Abort Revert_abort v` by simp[run_from_def] >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!m. _` kall_tac >>
  goal_assum (drule_at Any) >> metis_tac[RTC_RULES]
QED

Finalise abi_decode_reject_endpoint_aux

Theorem abi_decode_reject_endpoint:
  observer_region_closed ctx fn cut region /\
  (!s bb inst. (s.vs_current_bb,s.vs_inst_idx) IN region /\
    (s.vs_current_bb,s.vs_inst_idx) <> cut /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst ==> inst.inst_opcode <> INVOKE) /\
  (!s fuel v. (s.vs_current_bb,s.vs_inst_idx) = cut ==>
    run_from fuel ctx fn s <> Abort Revert_abort v) /\
  (s.vs_current_bb,s.vs_inst_idx) IN region /\ ~s.vs_halted /\
  run_from fuel ctx fn s = Abort Revert_abort v ==>
  ?u bb inst. RTC (abi_observer_step ctx fn cut) s u /\
    (u.vs_current_bb,u.vs_inst_idx) IN region /\
    (u.vs_current_bb,u.vs_inst_idx) <> cut /\ ~u.vs_halted /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\
    inst.inst_opcode <> INVOKE /\ step_inst_base inst u = Abort Revert_abort v
Proof
  strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
      simp[Once run_from_def]) >>
  irule abi_decode_reject_endpoint_aux >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
