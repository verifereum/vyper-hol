Theory requestCutFmpVisit
Ancestors
  requestCutReplayProofs requestCutOracleReplay requestCutOracleFrames e2eRequestCutDefs
  fmpStageOpSimMemCalls fmpStageCoverBack fmpStageRel
  lowerDloadExternalInputs lowerDloadRequestObservation
  contextCodegenRel ptrDiscipline memLocDefs venomExecSemantics
  venomWf venomState venomInst list rich_list

Theorem request_cut_fmp_visit:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  fmp_stage_ctx rp D C CT clip0 clipT fmp eom /\ inst_wf i /\
  frame_reachable clip0 C stk PG G tn fn i (s with vs_outcomes := []) /\
  active_inst fn i s /\ ~in_revert_forward fn s /\
  fmp_stage_rel D CT sm fmp0 raw0 eom restored stk PG G tn fn
    (s with vs_outcomes := []) lo (t with vs_outcomes := []) ts /\
  LENGTH s.vs_requests = k /\ LENGTH t.vs_requests = k /\
  s.vs_outcomes = t.vs_outcomes /\ i.inst_opcode <> INVOKE /\
  step_inst fuel CT i t = OK t' /\ k < LENGTH t'.vs_requests ==>
  ?s'. step_inst fuel C i s = OK s' /\ k < LENGTH s'.vs_requests /\
    (tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
       (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
     tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
       (s.vs_transient s.vs_call_ctx.cc_address) ==>
     request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests))
Proof
  strip_tac >>
  `LENGTH t.vs_requests < LENGTH t'.vs_requests` by simp[] >>
  drule_all ld_request_growth_external >> strip_tac >>
  Q.SUBGOAL_THEN `?g a v off sz ro rs salt scalars.
     (i.inst_opcode = CALL /\ i.inst_operands = [g;a;v;off;sz;ro;rs] /\
        scalars = [g;a;v;sz]) \/
     (MEM i.inst_opcode [STATICCALL;DELEGATECALL] /\
        i.inst_operands = [g;a;off;sz;ro;rs] /\ scalars = [g;a;sz]) \/
     (i.inst_opcode = CREATE /\ i.inst_operands = [v;off;sz] /\ scalars = [v;sz]) \/
     (i.inst_opcode = CREATE2 /\ i.inst_operands = [v;off;sz;salt] /\
        scalars = [v;sz;salt])`
    (qx_choosel_then [`g`,`a`,`v`,`off`,`sz`,`ro`,`rs`,`salt`,`scalars`] assume_tac)
  >-
    (qpat_assum `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
       (strip_assume_tac o REWRITE_RULE [MEM]) >>
     fs[MEM,inst_wf_def,LENGTH_EQ_NUM_compute] >>
     metis_tac[]) >>
  `s.vs_labels = t.vs_labels /\ s.vs_call_ctx = t.vs_call_ctx` by
    fs[fmp_stage_rel_def,fmp_frame_rel_def] >>
  `i.inst_opcode <> PHI /\ active_inst fn i (s with vs_outcomes := [])` by
    fs[MEM,loweringBudgetFrameOracleTransportTheory.active_inst_outcomes_update] >>
  `!op. MEM op i.inst_operands ==> ?w. eval_operand op s = SOME w` by
    (qpat_assum `step_inst fuel CT i t = OK t'` (fn step =>
       qpat_assum `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]`
         (fn opcode => assume_tac
           (MATCH_MP ld_external_target_operands_defined (CONJ opcode step)))) >>
     Cases >> simp[eval_operand_def] >> rpt strip_tac
     >- (drule_all fmp_stage_src_defined >>
         simp[optionTheory.IS_SOME_EXISTS,lookup_var_def]) >>
     metis_tac[eval_operand_def]) >>
  `!op. MEM op scalars ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `MEM op i.inst_operands /\
      (FILTER ($= op) i.inst_operands = [op] ==>
        !ops. mem_read_ops i = SOME ops \/ mem_write_ops i = SOME ops ==>
          ops.iao_ofst <> op)` by
       (irule ld_external_layout_scalars >>
        qpat_assum `(i.inst_opcode = CALL /\ _) \/ _` strip_assume_tac >>
        gvs[MEM] >> metis_tac[]) >>
     `?w. eval_operand op s = SOME w` by metis_tac[] >>
     `eval_operand op (s with vs_outcomes := []) = SOME w` by simp[] >>
     drule_all fmp_mem_external_scalar >> simp[]) >>
  `MEM off i.inst_operands /\ MEM sz i.inst_operands` by
    (qpat_assum `(i.inst_opcode = CALL /\ _) \/ _` strip_assume_tac >> fs[MEM]) >>
  `?p n. eval_operand off s = SOME p /\ eval_operand sz s = SOME n` by metis_tac[] >>
  `?ops. mem_read_ops i = SOME ops /\ ops.iao_ofst = off /\
    MEM (w2n p,w2n n) (source_memory_read_ranges i (s with vs_outcomes := []))` by
    (qpat_assum `(i.inst_opcode = CALL /\ _) \/ _` strip_assume_tac >>
     fs[MEM] >>
     qpat_x_assum `!op. _ ==> ?w. eval_operand op s = SOME w`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [DISJ_IMP_THM,FORALL_AND_THM]) >>
     gvs[mem_read_ops_def,source_memory_read_ranges_def,memory_range_of_operands_def]) >>
  `~in_revert_forward fn (s with vs_outcomes := []) /\
   eval_operand off (s with vs_outcomes := []) = SOME p` by
    fs[in_revert_forward_def,revert_forward_at_def] >>
  drule_all fmp_mem_external_input >> simp[read_memory_def] >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `?s'. step_inst fuel C i s = OK s'` by
    (irule request_step_relocated_backward >> asm_rewrite_tac[] >>
     qexistsl_tac [`CT`,`a`,`g`,`off`,`ro`,`rs`,`salt`,`scalars`,`sz`,`t`,`t'`,`v`] >>
     asm_rewrite_tac[]) >>
  `k < LENGTH s'.vs_requests` by metis_tac[external_ok_records_request, DECIDE ``k < SUC k``] >>
  qexists_tac `s'` >> simp[] >> strip_tac >>
  irule relocated_request_agrees >> simp[] >> conj_tac
  >- (irule request_step_relocated_shell >>
      qexistsl_tac [`C`,`CT`,`a`,`fuel`,`fuel`,`g`,`i`,`n`,`off`,`p`,`q`,`ro`,
        `rs`,`s`,`salt`,`scalars`,`sz`,`t`,`v`] >> fs[read_memory_def]) >>
  qexistsl_tac [`C`,`CT`,`fuel`,`fuel`,`i`,`i`,`s`,`t`,`tn`,`tn`] >>
  simp[] >>
  qpat_assum `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o MATCH_MP fmp_stage_rel_shared_store) >>
  simp[lowerDloadPtrCallTheory.dload_shared_store_def]
QED
