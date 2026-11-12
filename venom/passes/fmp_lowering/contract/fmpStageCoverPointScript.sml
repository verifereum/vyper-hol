(* Progress of coverage from a related source point. *)
Theory fmpStageCoverPoint
Ancestors
  fmpStageCoverPointBase fmpStageCoverRestore fmpStageCoverPointAlloc
  fmpStageCoverPointRetpc fmpStageCoverPointOrdinary
  fmpStageCoverInv fmpStageCoverBack fmpStageCoverMem
  fmpStageFmpSteps fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  o1LowerDloadReadiness o1PassContract ptrDiscipline contextCodegenRel
  venomStepProps venomInstProps venomExecSemantics venomExecProps venomWf
  venomState venomInst finite_map words list

Theorem fmp_cov_point_restored_next[local]:
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
  (MEM inst.inst_opcode [DALLOCA; INVOKE] \/ is_terminator inst.inst_opcode) /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_cov_stack C' stk ts stk' ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
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
  `inst.inst_opcode = DALLOCA` by gvs[] >>
  irule fmp_cov_point_alloc >>
  conj_tac >- (rpt strip_tac >> irule fmp_cov_endpoint_next >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[fmp_cov_source_next] >>
  rpt conj_tac >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
  Cases_on `restored`
  >- (irule fmp_cov_point_restored_next >>
      conj_tac >- first_assum ACCEPT_TAC >> rpt conj_tac >> metis_tac[]) >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn) \/
            inst.inst_opcode = DALLOCA`
  >- (`MEM inst.inst_opcode [DALLOCA; INVOKE] \/ is_terminator inst.inst_opcode` by
        (Cases_on `inst.inst_opcode = DALLOCA` >- simp[] >>
         Cases_on `inst.inst_opcode = INVOKE` >- simp[] >>
         `fmp_is_reclaim_point infos inst` by
           metis_tac[fmp_stage_plan_point] >>
         fs[fmpReclaimDefsTheory.fmp_is_reclaim_point_def,
            fmpReclaimDefsTheory.fmp_callee_info_def,
            fmpAnalysisDefsTheory.fmp_invoke_target_def, is_terminator_def] >> gvs[]) >>
      `fmp_cov D C C' vs vs' fmp eom stk' fn'
         (t2 with vs_inst_idx := SUC t.vs_inst_idx) \/
       (?sm1 lo1. fmp_stage_rel D C' sm1 (w2n vs'.vs_initial_fmp)
          (w2n fmp) eom T stk PG G tn fn s lo1 t ts)` by
        (irule fmp_cov_point_restore >> simp[] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (qexists_tac `ti'` >> fs[]) >>
         conj_tac >- metis_tac[] >>
         conj_tac >- (qexists_tac `inst` >> fs[]) >>
         conj_tac >- (qexistsl_tac [`G'`, `PG'`, `fuel`, `ti`, `tn'`] >> fs[]) >>
         qexistsl_tac [`lo`, `sm`] >> simp[]) >>
      irule fmp_cov_point_restored_next >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt conj_tac >> metis_tac[]) >>
  suspend "unrestored"
QED

Resume fmp_cov_point_next[unrestored]:
  `inst.inst_opcode <> DALLOCA /\
   ~((s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn))` by fs[] >>
  Cases_on `inst.inst_opcode = RETPC_PARAM`
  >- (irule fmp_cov_point_retpc >>
      conj_tac >- (rpt strip_tac >> irule fmp_cov_endpoint_next >> metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- metis_tac[fmp_cov_source_next] >>
      rpt conj_tac >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (`(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
      drule_all fmp_stage_invoke_inst >> strip_tac >>
      `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
            get_instruction bt t.vs_inst_idx = SOME ti` by
        metis_tac[lowerDloadPtrRawReachableTheory.active_inst_block_lookup] >>
      gvs[get_instruction_def]) >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by simp[] >>
  drule_all fmp_stage_kept_inst >> strip_tac >>
  `inst = ti` by
    metis_tac[lowerDloadPtrRawReachableTheory.active_inst_block_lookup,
              get_instruction_def, optionTheory.SOME_11] >>
  irule fmp_cov_point_ordinary >>
  conj_tac >- (rpt strip_tac >> irule fmp_cov_endpoint_zero >>
              drule_all fmp_cov_target_labels >> strip_tac >> metis_tac[]) >>
  conj_tac >- metis_tac[fmp_cov_source_next] >>
  simp[] >>
  conj_tac >- (qexists_tac `ti'` >> fs[]) >>
  conj_tac >- metis_tac[] >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  qexistsl_tac [`runner`, `inst`, `infos`, `ctx`] >> simp[] >>
  rpt strip_tac >>
  gvs[] >> drule_all fmp_cov_source_next >> simp[]
QED

Finalise fmp_cov_point_next
