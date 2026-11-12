(*
 * Facts the FmpLowering stage runner (fmpStageRunner) uses besides the
 * step lemmas: every frame_reachable state is live, no INVOKE calls the
 * context entry, a lowered function keeps its labels and shape, and the
 * root instructions the context entry runs first are straight-line.
 *
 * TOP-LEVEL:
 *   fmp_frame_reachable_not_halted - frame_reachable states are not halted
 *   fmp_frame_reachable_entry_last - the bottom frame is the context entry
 *   fmp_invoke_not_entry           - no INVOKE calls the context entry
 *   fmp_stage_rel_lowered          - the relation's target function is
 *                                    FmpLowering's, and its control fields
 *   fmp_stage_lowered_shape        - the lowered function's labels and shape
 *   fmp_run_insts_straight         - a run that leaves vs_prev_bb NONE has
 *                                    no terminator and no INVOKE
 *   fmp_active_next                - a non-terminator has a successor
 *   fmp_return_current_bb          - a return resumes the caller's block
 *)
Theory fmpStageRunnerFacts
Ancestors
  fmpStageRel fmpStepLayout fmpStepStructural ptrDiscipline o1PassContract
  lowerDloadPtrLiveFrames o1LowerDloadStackFunctions o1LowerDloadSourceEntry
  ctxLookupAgreeHelpers fmpLowerDefs venomExecProps
  analysisSimDefs venomInstProofs venomInstProofs1 venomExecProofs
  venomExecSemantics
  contextCodegenRel venomWf venomState venomInst list

(* Why: invoke_return and the block steps assume a live source state;
   only a halt ends a frame, and merge_callee_state keeps the caller's
   flag. *)
Theorem fmp_frame_reachable_not_halted:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    ~vs.vs_halted ==>
    ~s.vs_halted /\ EVERY (\f. ~f.cf_state.vs_halted) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[enters_block_def]
  >- (drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => once_rewrite_tac[th]) >> simp[])
  >- (`inst.inst_opcode <> INVOKE` by simp[] >>
      gvs[step_inst_non_invoke] >>
      drule step_inst_base_OK_preserves_halted >> simp[])
  >- (drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => once_rewrite_tac[th]) >> simp[])
  >- (drule eval_phis_only_updates_vs_vars >>
      disch_then (fn th => once_rewrite_tac[th]) >> gvs[setup_callee_def])
  >> qspec_then `\u. u.vs_halted` mp_tac bind_outputs_preserves >>
  simp[update_var_def] >> disch_then drule >>
  simp[adopt_return_fmp_def, merge_callee_state_def] >>
  CASE_TAC >> simp[]
QED

(* Why: the bottom frame runs the context entry, so the callee order
   (callee_first) puts every active function at or before it. *)
Theorem fmp_frame_reachable_entry_last:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    !name. C.ctx_entry = SOME name ==>
      (LAST (fn :: MAP (\f. f.cf_fn) stk)).fn_name = name
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[]
  >- metis_tac[lookup_function_selected_name]
  >> gvs[LAST_DEF]
QED

(* Why: fmp_stage_invoke_call assumes it.  The callee precedes its caller,
   which is the context entry or precedes it, and list_precedes is
   irreflexive. *)
Theorem fmp_invoke_not_entry:
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  callee_first names C.ctx_functions ==>
  C.ctx_entry <> SOME nm
Proof
  rpt strip_tac >>
  drule_all dload_frame_live_order >> strip_tac >>
  drule fmp_frame_reachable_entry_last >> disch_then drule >> strip_tac >>
  `MEM fn C.ctx_functions` by fs[] >>
  drule_all ld_active_callee_precedes >> strip_tac >>
  `callee.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  Cases_on `stk` >> gvs[]
  >- metis_tac[ld_list_precedes_irrefl] >>
  qpat_x_assum `!i j. _` (qspecl_then [`0`, `SUC (LENGTH t)`] mp_tac) >>
  `EL (LENGTH t) (h.cf_fn::MAP (\f. f.cf_fn) t) =
   LAST (h.cf_fn::MAP (\f. f.cf_fn) t)` by simp[LAST_EL] >>
  simp[] >> metis_tac[ld_list_precedes_trans, ld_list_precedes_irrefl]
QED

(* Why: the runner reads the target function and its control fields off
   the relation. *)
Theorem fmp_stage_rel_lowered:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  ?fn' infos ctx runner.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    fmp_stage_lowered infos ctx runner fn fn' /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    s.vs_halted = t.vs_halted
Proof
  simp[fmp_stage_rel_def, fmp_frame_rel_def] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

(* Why: the target function has the source's labels, so its instructions
   are fetched by label and index, and its first block, like the
   source's, has no PHI. *)
Theorem fmp_stage_lowered_shape:
  fmp_stage_lowered infos ctx runner fn fn' /\ wf_function fn ==>
  fn_labels fn' = fn_labels fn /\ fn_entry_label fn' = fn_entry_label fn /\
  (first_block_no_phi fn ==>
   EVERY bb_well_formed fn'.fn_blocks /\ first_block_no_phi fn')
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  `fmp_lower_function ctx sp fn = SOME (fn',sp')` by
    simp[fmp_lower_function_def] >>
  imp_res_tac fmp_lower_function_preserves_labels >>
  imp_res_tac fmp_lower_function_preserves_entry_label >> simp[] >>
  strip_tac >> drule_all fmp_lower_function_structure >> simp[]
QED

Theorem run_insts_prev_bb_some[local]:
  !L k C t t'.
    run_insts k C L t = OK t' /\ t.vs_prev_bb <> NONE ==>
    t'.vs_prev_bb <> NONE
Proof
  Induct >> simp[run_insts_def] >> rpt gen_tac >>
  Cases_on `step_inst k C h t` >> simp[] >> strip_tac >>
  `v.vs_prev_bb <> NONE` suffices_by metis_tac[] >>
  Cases_on `is_terminator h.inst_opcode`
  >- (`h.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_invoke] >>
      gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_prev_bb >> simp[]) >>
  drule_all step_preserves_prev_bb >> simp[]
QED

(* Why: the context entry's root runs before its first related point
   (fmp_stage_entry), from vs_prev_bb = NONE to a point that still has it.
   An INVOKE fails at fuel 0, and a terminator that steps OK jumps, which
   sets vs_prev_bb; so the run is a straight-line prefix that exec_block
   skips (exec_block_skip_prefix). *)
Theorem fmp_run_insts_straight:
  !L t t'.
    run_insts 0 C L t = OK t' /\ t.vs_prev_bb = NONE /\
    t'.vs_prev_bb = NONE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) L
Proof
  Induct >> simp[run_insts_def] >> rpt gen_tac >>
  Cases_on `step_inst 0 C h t` >> simp[] >> strip_tac >>
  `h.inst_opcode <> INVOKE` by
    (strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[Once step_inst_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[Once run_blocks_def]) >>
  `~is_terminator h.inst_opcode` by
    (strip_tac >>
     `v.vs_prev_bb <> NONE` by
       (gvs[step_inst_non_invoke] >>
        drule_all step_inst_base_term_prev_bb >> simp[]) >>
     metis_tac[run_insts_prev_bb_some]) >>
  simp[] >> first_x_assum irule >>
  qexistsl_tac [`v`, `t'`] >> simp[] >>
  metis_tac[step_preserves_prev_bb]
QED

(* Why: the INVOKE case names the instruction after the call; a
   well-formed block ends in its only terminator. *)
Theorem fmp_active_next:
  wf_function fn /\ active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  s'.vs_current_bb = s.vs_current_bb ==>
  ?next. active_inst fn next (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[active_inst_def, wf_function_def] >> strip_tac >> gvs[] >>
  `bb_well_formed bb` by metis_tac[] >>
  drule_all non_terminator_not_last >> strip_tac >>
  qexists_tac `bb` >> simp[]
QED

(* Why: merge_callee_state keeps the caller's control fields, so the
   instruction after the call is fetched from the caller's block. *)
Theorem fmp_return_current_bb:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s se)) =
    SOME s' ==>
  s'.vs_current_bb = s.vs_current_bb
Proof
  qspec_then `\u. u.vs_current_bb` mp_tac bind_outputs_preserves >>
  simp[update_var_def] >> disch_then (fn th => strip_tac >> drule th) >>
  simp[adopt_return_fmp_def, merge_callee_state_def] >>
  CASE_TAC >> simp[]
QED
