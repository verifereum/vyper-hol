Theory requestCutFmpCursor
Ancestors
  fmpStageCoverInv fmpStageCoverMem fmpStageOpSteps fmpStageOpBase
  fmpStageControl fmpCoverInvokeIndex fmpStageRel fmpReclaimDefs fmpAnalysisDefs
  lowerDloadPtrRawReachable lowerDloadPtrForward concretizeLayoutLocalReturn
  contextCodegenRel o1PassContract ptrDiscipline o1LowerDloadShared
  venomExecSemantics venomWf venomInst venomState arithmetic finite_map list

(* An external request at a covered point cannot come from a restore,
   allocation expansion or rewritten call protocol instruction. *)
Theorem fmp_external_point_origin[local]:
  fmp_stage_ctx rp D C CT vs vt fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D CT sm (w2n vt.vs_initial_fmp) (w2n fmp) eom restored
    stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name CT.ctx_functions = SOME fn' /\
  active_inst fn' ti t /\ MEM ti.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] ==>
  ti = inst /\ ~in_revert_forward fn s
Proof
  strip_tac >>
  drule_all fmp_stage_active_facts >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_cov_target_labels >> strip_tac >>
  drule_all fmp_cov_frame_pos >>
  disch_then (qx_choosel_then [`infos`,`ctx0`,`runner`] strip_assume_tac) >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  qpat_x_assum `!bb. lookup_block _ _ = _ ==> _` drule >> strip_tac >>
  `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx0 fn)
    (fmp_stage_root infos ctx0 fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
    (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx0 fn)
     then 1 else 0) /\ ~MEM inst.inst_opcode [DALLOCA;RETPC_PARAM]` by
    (spose_not_then assume_tac >>
     `?bt'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt' /\
       t.vs_inst_idx < LENGTH bt'.bb_instructions /\
       fmp_inserted_op (EL t.vs_inst_idx bt'.bb_instructions).inst_opcode` by
       (irule fmp_stage_inserted_at >> simp[] >>
        qexistsl_tac [`C`,`CT`,`D`,`bb`,`ctx0`,`eom`,`fmp`,`fn`,
          `s.vs_inst_idx`,`infos`,`rp`,`runner`,`vs`,`vt`] >> simp[] >>
        `fmp_stage_tidx (fmp_stage_plan infos ctx0 fn) (fmp_stage_root infos ctx0 fn)
          s.vs_current_bb bb.bb_instructions s.vs_inst_idx +
          (if (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx0 fn)
           then 1 else 0) <
         fmp_stage_tidx (fmp_stage_plan infos ctx0 fn) (fmp_stage_root infos ctx0 fn)
          s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx)` by
          metis_tac[fmp_cov_tidx_lt] >>
        rpt conj_tac
        >- (Cases_on `restored` >>
            Cases_on `(s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx0 fn)` >>
            fs[] >> decide_tac)
        >- (Cases_on `s.vs_inst_idx = 0` >> simp[] >> decide_tac) >>
        strip_tac >> metis_tac[MEM]) >>
     gvs[get_instruction_def,fmp_inserted_op_def,MEM]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (`(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
      drule_all fmp_stage_invoke_inst >> strip_tac >> gvs[get_instruction_def,MEM]) >>
  `~MEM inst.inst_opcode [DALLOCA;INVOKE;RETPC_PARAM]` by fs[MEM] >>
  drule_all fmp_stage_kept_inst >> strip_tac >>
  `ti = inst` by gvs[get_instruction_def] >> simp[] >>
  `~MEM inst.inst_opcode [RETURNDATACOPY; REVERT]` by
    (qpat_x_assum `ti = inst` SUBST_ALL_TAC >> fs[MEM]) >>
  irule active_inst_not_revert_forward >> fs[o1_fn_shape_def,wf_function_def] >>
  qexists_tac `inst` >> simp[]
QED

Theorem request_cut_fmp_cursor:
  fmp_stage_ctx rp D C CT vs vt fmp eom /\
  ALL_DISTINCT (fn_labels fn') /\ active_inst fn' i t /\
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  fmp_cov D C CT vs vt fmp eom stk' fn' t ==>
  ?stk PG G tn fn s sm lo ts restored.
    frame_reachable vs C stk PG G tn fn i s /\ active_inst fn i s /\
    ~in_revert_forward fn s /\
    fmp_stage_rel D CT sm (w2n vt.vs_initial_fmp) (w2n fmp) eom restored
      stk PG G tn fn s lo t ts /\
    LENGTH s.vs_requests = LENGTH t.vs_requests /\
    s.vs_outcomes = t.vs_outcomes
Proof
  strip_tac >> drule_all active_inst_block_lookup >> strip_tac >>
  qpat_x_assum `fmp_cov _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [fmp_cov_def])
  >- (`t.vs_inst_idx = t1.vs_inst_idx` by
        (Cases_on `t.vs_inst_idx < t1.vs_inst_idx` >> fs[] >>
         qpat_x_assum `!i. t.vs_inst_idx <= i /\ _ ==> _`
           (qspec_then `t.vs_inst_idx` mp_tac) >>
         fs[get_instruction_def,fmp_inserted_op_def,MEM] >> decide_tac) >>
      `t1 = t` by
        (qpat_x_assum `!k. fmp_target_run _ _ _ _ _ _` (qspec_then `0` mp_tac) >>
         simp[] >> strip_tac >> drule fmp_target_run_zero >> simp[]) >>
      qpat_x_assum `t1 = t` SUBST_ALL_TAC >>
      drule_all fmp_external_point_origin >> strip_tac >> gvs[] >>
      qexistsl_tac [`stk`,`PG`,`G`,`tn`,`fn`,`s`,`sm`,`lo`,`ts`,`restored`] >> simp[] >>
      fs[fmp_stage_rel_def,ld_shared_agree_def] >> metis_tac[LIST_REL_LENGTH]) >>
  `p <= t.vs_inst_idx` by decide_tac >>
  `bb' = bb` by fs[] >>
  qpat_x_assum `bb' = bb` SUBST_ALL_TAC >>
  drule_all revert_forward_pair_interval_opcode >> fs[MEM]
QED
