(* Restored DALLOCA progress; the shared coverage boundaries are parameters. *)
Theory fmpStageCoverPointAlloc
Ancestors
  fmpStageCoverInv fmpStageCoverBack fmpStageCoverMem
  fmpStageFmpSteps fmpStageOpSteps fmpStageOpBase fmpStageControl fmpStageRel
  o1PassContract ptrDiscipline venomStepProps venomInstProps venomExecSemantics venomState
  venomInst finite_map words list

Theorem fmp_cov_point_alloc:
  (!fn' C' name ti t fuel t2 n u.
    ALL_DISTINCT (fn_labels fn') /\
    lookup_function name C'.ctx_functions = SOME fn' /\ active_inst fn' ti t /\
    ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C' ti t = OK t2 /\ 0 < n /\
    (!k. fmp_target_run k C' name t n u) ==>
    !k. fmp_target_run k C' name
      (t2 with vs_inst_idx := SUC t.vs_inst_idx) (n-1) u) /\
  (!rpolicy D C C' vs vs' fmp eom stk PG G tn fn inst s fuel s1.
    fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ~s.vs_halted /\ ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel C inst s = OK s1 ==>
    ?inst2.
      frame_reachable vs C stk PG (step_prov PG G inst s1)
        (step_taint inst s s1 tn) fn inst2
        (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
      active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
      ~(s1 with vs_inst_idx := SUC s.vs_inst_idx).vs_halted) /\
  (!D C C' vs vs' (fmp :256 word) eom stk' fn' ti t fuel t2 n u
      stk PG G tn fn inst s sm lo ts restored bb'.
    ALL_DISTINCT (fn_labels fn') /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    active_inst fn' ti t /\ ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
    step_inst fuel C' ti t = OK t2 /\ 0 < n /\
    (!k. fmp_target_run k C' fn.fn_name t n u) /\
    t.vs_current_bb = u.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx + n /\
    frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
    ~s.vs_halted /\
    (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/ is_terminator inst.inst_opcode) /\
    fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom restored
      stk PG G tn fn s lo u ts /\ fmp_cov_stack C' stk ts stk' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    (!i. SUC t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
      i < LENGTH bb'.bb_instructions /\
      fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode) ==>
    fmp_cov D C C' vs vs' fmp eom stk' fn'
      (t2 with vs_inst_idx := SUC t.vs_inst_idx)) /\
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\ active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\
  active_inst fn' ti' (t2 with vs_inst_idx := SUC t.vs_inst_idx) /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\
  fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
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
  `terminates (step_inst fuel C inst s)` by
    (irule fmp_stage_back_fmp_ops >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`fmp0` |-> `w2n vs'.vs_initial_fmp`,
                  `raw0` |-> `w2n fmp`, `k` |-> `fuel`,
                  `r` |-> `step_inst fuel C inst s`] fmp_stage_dalloca_step) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  qpat_x_assum `!rpolicy D C C' vs vs' fmp eom stk PG G tn fn inst s fuel s1. _`
    (drule_all_then strip_assume_tac) >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `t1.vs_current_bb = t.vs_current_bb` by
    (drule_all fmp_cov_frame_pos >> simp[] >> metis_tac[]) >>
  `t1.vs_inst_idx = t.vs_inst_idx + 4` by
    (qpat_x_assum `!k'. fmp_target_run _ _ _ _ _ _`
      (qspec_then `0` mp_tac) >> rw[fmp_target_run_def] >> simp[]) >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[lowerDloadPtrRawReachableTheory.active_inst_block_lookup] >>
  `!i. SUC t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
       i < LENGTH bt.bb_instructions /\
       fmp_inserted_op (EL i bt.bb_instructions).inst_opcode` by
    (rpt strip_tac >>
     `i < fmp_stage_tidx (fmp_stage_plan infos ctx fn)
        (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions
        (SUC s.vs_inst_idx)` by
       (fs[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
        Cases_on `fmp_stage_root infos ctx fn` >- gvs[] >>
        rename1 `fmp_stage_root infos ctx fn = SOME root` >>
        Cases_on `root` >>
        rename1 `fmp_stage_root infos ctx fn = SOME (rl,rp)` >>
        Cases_on `s.vs_current_bb = rl` >>
        Cases_on `rp <= s.vs_inst_idx` >> fs[] >>
        rpt IF_CASES_TAC >> fs[] >> decide_tac) >>
     mp_tac (Q.INST [`i` |-> `i`, `idx` |-> `s.vs_inst_idx`,
                     `lbl` |-> `s.vs_current_bb`] fmp_stage_inserted_at) >>
     (impl_tac >- (fs[] >> Cases_on `s.vs_inst_idx = 0` >> fs[] >>
       Cases_on `(s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)` >>
       fs[])) >>
     strip_tac >> gvs[]) >>
  first_x_assum irule >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ F _ _ _ _ _ _ _ _ _`
    (irule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl [`4`, `inst2`] >> fs[] >>
  qpat_x_assum `frame_reachable _ _ _ _ _ _ _ inst2 _` mp_tac >>
  simp[]
QED
