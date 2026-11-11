Theory concretizePtrCoverageStaticMemReachability
Ancestors
  ptrDiscipline contextRawReachable venomExecProofs venomExecSemantics
  stepWriteFootprintBase venomInstProofs contextCodegenRel contextCodegenRelProps

Theorem ptr_run_defs_frame_lift:
  (!fuel ctx inst s. !vs0 stk PG G tn fn.
    frame_reachable vs0 ctx stk PG G tn fn inst s /\ active_inst fn inst s ==>
    (!t next. ~is_terminator inst.inst_opcode /\
      step_inst fuel ctx inst s = OK t /\
      active_inst fn next (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ?PG' G' tn'. frame_reachable vs0 ctx stk PG' G' tn' fn next
        (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
    (!ret t. step_inst fuel ctx inst s = IntRet ret t ==>
      ?PG' G' tn' ri u n. frame_reachable vs0 ctx stk PG' G' tn' fn ri u /\
        active_inst fn ri u /\ step_inst n ctx ri u = IntRet ret t)) /\
  (!fuel ctx bb s. !vs0 stk PG G tn fn inst.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    (!t s1 next. exec_block fuel ctx bb s = OK t /\ ~t.vs_halted /\
      enters_block fn t s1 /\ active_inst fn next s1 ==>
      ?PG' G' tn'. frame_reachable vs0 ctx stk PG' G' tn' fn next s1) /\
    (!ret t. exec_block fuel ctx bb s = IntRet ret t ==>
      ?PG' G' tn' ri u n. frame_reachable vs0 ctx stk PG' G' tn' fn ri u /\
        active_inst fn ri u /\ step_inst n ctx ri u = IntRet ret t)) /\
  (!fuel ctx fn s. !vs0 stk.
    (!s1 inst. enters_block fn s s1 /\ active_inst fn inst s1 ==>
      ?PG G tn. frame_reachable vs0 ctx stk PG G tn fn inst s1) ==>
    !ret t. run_blocks fuel ctx fn s = IntRet ret t ==>
      ?PG' G' tn' ri u n. frame_reachable vs0 ctx stk PG' G' tn' fn ri u /\
        active_inst fn ri u /\ step_inst n ctx ri u = IntRet ret t)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume ptr_run_defs_frame_lift[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[frame_reachable_next]) >>
  rpt strip_tac >> metis_tac[]
QED

Resume ptr_run_defs_frame_lift[invoke]:
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      once_rewrite_tac[step_inst_def] >> simp[] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      first_x_assum (qspecl_then [`vs0`,
        `<| cf_fn := fn; cf_inst := inst; cf_state := s;
            cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk`] mp_tac) >>
      (impl_tac >- (rpt strip_tac >> metis_tac[frame_reachable_call])) >>
      strip_tac >> drule frame_reachable_ret >> simp[] >>
      disch_then drule >> disch_then drule >>
      disch_then (qspec_then `next` mp_tac) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  once_rewrite_tac[step_inst_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Resume ptr_run_defs_frame_lift[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `active_inst fn inst s` by (irule lookup_instruction_active >> simp[]) >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >> strip_tac >> gvs[]
  >>~- ([`step_inst fuel ctx inst s = OK u`], suspend "block_ok")
  >> qpat_x_assum `!inst s''. _` kall_tac >> metis_tac[]
QED
Resume ptr_run_defs_frame_lift[block_ok]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  rename1 `step_inst fuel ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[]
  >>~- ([`(if u.vs_halted then Halt u else OK u) = IntRet ret t`],
    Cases_on `u.vs_halted` >> gvs[])
  >>~- ([`(if u.vs_halted then Halt u else OK u) = OK t`],
    Cases_on `u.vs_halted` >> gvs[] >> metis_tac[frame_reachable_block]) >>
  (Cases_on `get_instruction bb (SUC s.vs_inst_idx)`
   >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
       once_rewrite_tac[exec_block_def] >> simp[])) >>
  rename1 `get_instruction bb (SUC s.vs_inst_idx) = SOME ni` >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `active_inst fn ni (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule lookup_instruction_active >> simp[]) >>
  `?PG1 G1 tn1. frame_reachable vs0 ctx stk PG1 G1 tn1 fn ni
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  metis_tac[]
QED
Resume ptr_run_defs_frame_lift[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_blocks_def] >>
  Cases_on `fuel` >> simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `enters_block fn s (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (simp[enters_block_def] >> metis_tac[]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  (Cases_on `get_instruction bb (phi_prefix_length bb.bb_instructions)`
   >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
       once_rewrite_tac[exec_block_def] >> simp[])) >>
  rename1 `get_instruction bb (phi_prefix_length bb.bb_instructions) = SOME head` >>
  `active_inst fn head (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    (irule lookup_instruction_active >> simp[]) >>
  `?PG G tn. frame_reachable vs0 ctx stk PG G tn fn head
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by metis_tac[]
  >>~- ([`run_blocks n ctx fn s'' = IntRet ret t`],
    `!s1 inst. enters_block fn s'' s1 /\ active_inst fn inst s1 ==>
       ?PG G tn. frame_reachable vs0 ctx stk PG G tn fn inst s1` by
      (rpt strip_tac >> metis_tac[]) >> metis_tac[]) >>
  metis_tac[]
QED
Finalise ptr_run_defs_frame_lift

Theorem ptr_frame_completed_next:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK t /\
  active_inst fn next (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?PG' G' tn'. frame_reachable vs0 ctx stk PG' G' tn' fn next
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  metis_tac[ cj 1 ptr_run_defs_frame_lift ]
QED

Theorem ptr_raw_reachable_frame:
  !vs ctx fn inst s. raw_reachable vs ctx fn inst s ==>
    ?stk PG G tn. frame_reachable vs ctx stk PG G tn fn inst s
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> metis_tac[frame_reachable_entry])
  >- (rpt strip_tac >> metis_tac[ptr_frame_completed_next])
  >- (rpt strip_tac >> metis_tac[frame_reachable_block]) >>
  rpt strip_tac >> metis_tac[frame_reachable_call]
QED
