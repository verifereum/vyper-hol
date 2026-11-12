(* Progress of coverage from a related source point. *)
Theory fmpStageCoverPoint
Ancestors
  fmpStageCoverInv fmpStageCoverBack fmpStageCoverMem
  fmpStageFmpSteps fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  o1LowerDloadReadiness o1PassContract ptrDiscipline contextCodegenRel
  venomStepProps venomInstProps venomExecSemantics venomExecProps venomWf
  venomState venomInst finite_map words list

Theorem fmp_cov_source_next[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK s1 ==>
  ?inst2.
    frame_reachable vs C stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    ~(s1 with vs_inst_idx := SUC s.vs_inst_idx).vs_halted
Proof
  rpt strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  drule_all ld_nonterminator_successor >> strip_tac >>
  qexists_tac `inst2` >> simp[] >>
  conj_tac >- metis_tac[frame_reachable_next] >>
  metis_tac[step_inst_ok_halted]
QED

Theorem fmp_cov_point_next:
  (!fn' C' name ti t fuel t2 n u.
    ALL_DISTINCT (fn_labels fn') /\
    lookup_function name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
    ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C' ti t = OK t2 /\ 0 < n /\
    (!k. fmp_target_run k C' name t n u) ==>
    !k. fmp_target_run k C' name
      (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n-1) u) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\ active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\
  active_inst fn' ti' (t2 with vs_inst_idx := SUC t.vs_inst_idx) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/
               is_terminator inst.inst_opcode) /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt strip_tac >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
  Cases_on `restored`
  >- suspend "restored"
  >> suspend "unrestored"
QED

Resume fmp_cov_point_next[restored]:
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[] >> drule_all fmp_stage_invoke_inst >> strip_tac >>
      `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
            get_instruction bt t.vs_inst_idx = SOME ti` by
        metis_tac[lowerDloadPtrRawReachableTheory.active_inst_block_lookup] >>
      gvs[get_instruction_def]) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (`~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
        (rpt strip_tac >> gvs[is_terminator_def]) >>
      `~T ==> ~is_terminator inst.inst_opcode` by simp[] >>
      drule_all fmp_stage_target_inst >> strip_tac >>
      `inst = ti` by metis_tac[lowerDloadPtrRawReachableTheory.active_inst_block_lookup,
                                optionTheory.SOME_11] >> gvs[]) >>
  cheat
QED

Resume fmp_cov_point_next[unrestored]:
  cheat
QED

Finalise fmp_cov_point_next
