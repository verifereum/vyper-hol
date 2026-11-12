(*
 * FmpLowering's coverage (fmpStageCoverage): the invariant fmp_cov holds
 * at the context entry and is kept by a step within a block.  A step from
 * a state inside an inserted run moves along the run; a step from a
 * related point uses the step lemmas of fmpStageOpSteps and
 * fmpStageFmpSteps on the source step fmpStageCoverBack gives (first
 * restoring with fmp_stage_restore where the lemma needs restored = T); a
 * step in a revert forwarding's tail stays in it.
 *
 * TOP-LEVEL:
 *   fmp_cov_entry - the target's entry state is covered
 *   fmp_cov_next  - a non-terminator, non-INVOKE target step keeps fmp_cov
 *)
Theory fmpStageCoverStep
Ancestors
  fmpStageCoverRun fmpStageCoverPoint
  fmpStageCoverInv fmpStageCoverCall fmpStageCoverBack fmpStageCoverMem
  fmpStageBlockSim fmpStageFmpSteps fmpStageOpSteps fmpStageOpBase
  fmpStageControl fmpStageRel ptrDiscipline contextCodegenRel o1PassContract
  passSimulationDefs venomExecSemantics venomState venomInst finite_map
  words list unitMemInv concretizeStageLookup fmpStageOpBaseActual
  fmpStepLayout fmpStepStructural fmpAnalysisProps fmpLowerDefs unitTransformDefs lowerDloadPtrRawReachable venomWf

Theorem fmp_cov_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C'.ctx_entry = SOME name /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  enters_block fn'
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>) t /\
  active_inst fn' ti t ==>
  fmp_cov D C C' vs vs' fmp eom [] fn' t
Proof
  rpt strip_tac >>
  `?fn sl. C.ctx_entry = SOME name /\
           lookup_function name C.ctx_functions = SOME fn /\
           fn_entry_label fn = SOME sl` by
    (fs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def,
        mem_inv_raw_reachable, ctx_pass_stage_def] >> gvs[] >> metis_tac[]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
      (o1_walk_view rpolicy 3) C C'` by fs[fmp_stage_ctx_def] >>
  drule_all ctx_pass_stage_lookup >> strip_tac >>
  qpat_x_assum `_.fpo_function = _` kall_tac >> gvs[] >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_name] >>
  `lookup_function fn.fn_name C'.ctx_functions = SOME fn'` by simp[] >>
  drule_all fmp_stage_actual_witness >> strip_tac >>
  `o1_fn_shape C fn` by
    (fs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `first_block_no_phi fn /\ wf_function fn` by fs[o1_fn_shape_def] >>
  `first_block_no_phi fn' /\ fn_entry_label fn' = fn_entry_label fn` by
    (fs[fmp_stage_lowered_def] >>
     `fmp_lower_function ctx0 sp fn = SOME (fn',sp')` by
       simp[fmp_lower_function_def] >>
     drule fmp_lower_function_preserves_entry_label >> strip_tac >>
     drule_all fmp_lower_function_first_block_no_phi >> gvs[]) >>
  gvs[] >>
  drule_all fmp_stage_back_entry >> strip_tac >>
  drule_all fmp_stage_entry >> strip_tac >>

  `t = vs' with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (Cases_on `fn'.fn_blocks` >>
     fs[fn_entry_label_def, entry_block_def, first_block_no_phi_def] >>
     `phi_prefix_length h.bb_instructions = 0 /\
      (!u. eval_phis u h.bb_instructions = OK u)` by
       (Cases_on `h.bb_instructions` >>
        fs[phi_prefix_length_def, eval_phis_def]) >>
     fs[enters_block_def, lookup_block_def, FIND_thm] >> gvs[]) >>
  `s1 = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (Cases_on `fn.fn_blocks` >>
     fs[fn_entry_label_def, entry_block_def, first_block_no_phi_def] >>
     `phi_prefix_length h.bb_instructions = 0 /\
      (!u. eval_phis u h.bb_instructions = OK u)` by
       (Cases_on `h.bb_instructions` >>
        fs[phi_prefix_length_def, eval_phis_def]) >>
     fs[enters_block_def, lookup_block_def, FIND_thm] >> gvs[]) >>
  `frame_reachable vs C [] [] FEMPTY entry_taint fn inst s1` by
    (irule frame_reachable_entry >> metis_tac[]) >>
  `~s1.vs_halted` by
    fs[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `lookup_function fn.fn_name C'.ctx_functions = SOME fn'` by simp[] >>
  drule_all fmp_cov_frame_pos >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `?bb. lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s1.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_block_lookup] >>
  `s1.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
   t.vs_current_bb = s1.vs_current_bb` by simp[] >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
  `?bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
          n = t1.vs_inst_idx` by
    (qpat_assum `!k. fmp_target_run _ _ _ _ _ _`
       (qspec_then `0` mp_tac) >>
     pure_rewrite_tac[fmp_target_run_def] >> strip_tac >>
     gvs[] >> metis_tac[]) >>
  `0 < LENGTH bb.bb_instructions` by fs[get_instruction_def] >>
  `!i. i < t1.vs_inst_idx ==>
       i < LENGTH bb'.bb_instructions /\
       fmp_inserted_op (EL i bb'.bb_instructions).inst_opcode` by
    (gen_tac >> disch_tac >>
     `i < fmp_stage_tidx (fmp_stage_plan infos ctx fn)
            (fmp_stage_root infos ctx fn) s1.vs_current_bb
            bb.bb_instructions (SUC 0)` by
       (irule arithmeticTheory.LESS_TRANS >>
        qexists_tac `t1.vs_inst_idx` >> conj_tac >- simp[] >>
        simp[] >>
        irule (SRULE [] (Q.INST [`idx` |-> `0`] (cj 2 fmp_cov_tidx_lt)))) >>
     mp_tac (Q.INST [`idx` |-> `0`, `i` |-> `i`,
       `infos` |-> `infos`, `ctx` |-> `ctx`, `runner` |-> `runner`,
       `fn` |-> `fn`, `lbl` |-> `s1.vs_current_bb`, `bb` |-> `bb`]
       fmp_stage_inserted_at) >>
     simp[] >> impl_tac >- (gvs[] >> strip_tac >> gvs[] >>
       Cases_on `(t1.vs_current_bb,0) IN FDOM (fmp_stage_plan infos ctx fn)` >> fs[]) >>
     strip_tac >> gvs[]) >>
  pure_rewrite_tac[fmp_cov_def] >> disj1_tac >>
  qexistsl [`[]`, `[]`, `FEMPTY`, `entry_taint`, `fn`, `inst`,
            `s1`, `FEMPTY`, `w2n vs'.vs_initial_fmp`, `t1`, `[]`, `F`, `bb'`] >>
  simp[fmp_cov_stack_def] >> gvs[]
QED

Theorem fmp_cov_next:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs' C' stk' PG' G' tn' fn' ti t /\
  fmp_cov D C C' vs vs' fmp eom stk' fn' t /\ active_inst fn' ti t /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t2 /\
  active_inst fn' ti' (t2 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  fmp_cov D C C' vs vs' fmp eom stk' fn'
    (t2 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  rpt strip_tac >>
  qpat_x_assum `fmp_cov _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [fmp_cov_def])
  >- (Cases_on `t.vs_inst_idx = t1.vs_inst_idx`
      >- (`t1 = t` by
            (qpat_x_assum `!k. fmp_target_run _ _ _ _ _ _`
               (qspec_then `0` mp_tac) >>
             simp[] >> metis_tac[fmp_target_run_zero]) >>
          qpat_x_assum `t1 = t` SUBST_ALL_TAC >>
          irule fmp_cov_point_next >>
          conj_tac >- metis_tac[fmp_cov_run_step] >>
          rpt conj_tac >> metis_tac[]) >>
      irule fmp_cov_prefix_next >>
      rpt conj_tac >> metis_tac[arithmeticTheory.LESS_OR_EQ]) >>
  irule fmp_cov_tail_next >> metis_tac[]
QED
