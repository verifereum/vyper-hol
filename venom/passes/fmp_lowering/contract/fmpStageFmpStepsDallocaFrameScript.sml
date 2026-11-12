Theory fmpStageFmpStepsDallocaFrame
Ancestors
  fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLowerSequenceExec fmpLedgerProps fmpAliasProps
  fmpReclaimDefs fmpAnalysisDefs venomState finite_map words list
  fmpStageFmpStepsDallocaData fmpStageFmpStepsDallocaLedger

Theorem fmp_dalloca_frame:
 fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
 frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
 ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
 step_inst k C inst s = OK s1 /\
 fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tn.t_var s t /\
 fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\
 eb = fmp_frame_base raw0 stk /\
 fmp_stage_lowered infos ctx runner fn fn' /\
 fmp_stage_root infos ctx fn = SOME (rl,rp) /\
 ~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp) /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 fmp_base_analyze (fn_insts fn) = SOME env /\
 fmp_reclaim_states infos fn = SOME states /\
 df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
 MAP (\r. r.fr_mark) regions = SND (fmp_pop_at infos fn
   (liveness_analyze fn) env (s.vs_current_bb,s.vs_inst_idx) inst st) /\
 fmp_ledger_ok (fn_insts fn) env t lo regions /\
 EVERY (\r. elo <= r.fr_lo) regions /\
 fmp_ledger_link sm eb lo regions /\ fmp_frame_covers sm env eb lo G /\
 ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
 EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned;runner] /\
 EVERY (\v. ~MEM v (MAP (\r. r.fr_mark) regions))
   [plus31;mask;aligned;runner;out] /\
 w2n s.vs_fmp + z < dimword (:256) /\ lo+z < dimword (:256) /\
 s1 = update_var out s.vs_fmp
   (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
 t1 = (update_var runner (n2w (lo+z))
   (update_var out (n2w lo)
    (update_var aligned a (update_var mask m (update_var plus31 p t)))))
   with vs_inst_idx := j /\
 j = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
   (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions
   (SUC s.vs_inst_idx) /\
 sm1 = (if z=0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) ==>
 fmp_frame_rel sm1 fmp0 raw0 eb elo (lo+z) F fn fn' PG
   (step_prov PG G inst s1) (step_taint inst s s1 tn).t_var
   (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1
Proof
 strip_tac >>
 drule_all fmp_stage_frame_facts >> strip_tac >>
 `wf_function fn` by gvs[o1PassContractTheory.o1_fn_shape_def] >>
 `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
   metis_tac[simplifyCfgDefsTheory.lookup_block_member_label] >>
 `s.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL s.vs_inst_idx bb.bb_instructions` by
   (fs[contextCodegenRelTheory.active_inst_def] >>
    imp_res_tac venomExecProofsTheory.wf_lookup_block >> gvs[]) >>
 `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
   fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
 qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
   (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
 `!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm1 k = SOME v` by
   (qx_gen_tac `key` >> qx_gen_tac `value` >>
    PairCases_on `key` >> PairCases_on `value` >> strip_tac >>
    Cases_on `z=0` >> gvs[] >> simp[FLOOKUP_UPDATE] >>
    IF_CASES_TAC >> gvs[fmp_sites_ok_def] >>
    qpat_x_assum `!b z c id. FLOOKUP sm _ = _ ==> 0 < z /\ _` drule >>
    simp[] >> decide_tac) >>
 `w2n s1.vs_fmp = w2n s.vs_fmp + z` by
   simp[update_var_def, wordsTheory.w2n_n2w] >>
 drule_all fmp_dalloca_ledger_step >> strip_tac >>
 `EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned] /\
  ~MEM runner (fn_ir_vars fn)` by fs[] >>
 drule_all fmp_dalloca_env_updates >> strip_tac >>
 drule_all fmp_dalloca_params_updates >> strip_tac >>
 simp[fmp_frame_rel_def] >> qexistsl [`infos`,`ctx`,`runner`] >>
 gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
 rpt conj_tac
 >- (gvs[fmp_frontier_rel_def] >> simp[wordsTheory.w2n_n2w] >> decide_tac)
 >- (rpt gen_tac >> Cases_on `z=0` >- (simp[] >> metis_tac[]) >>
     simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[] >> metis_tac[])
 >- (strip_tac >> gvs[] >> decide_tac) >>
 qexists_tac `<|fr_mark := out;
                fr_site := (EL s.vs_inst_idx bb.bb_instructions).inst_id;
                fr_lo := lo; fr_hi := lo+z|> :: regions` >> simp[]
QED
