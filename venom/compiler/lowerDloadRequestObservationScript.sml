Theory lowerDloadRequestObservation
Ancestors
  lowerDloadOracleSelection lowerDloadExternalInputs lowerDloadExternalBackward
  lowerDloadReachableDiscipline lowerDloadNormalData lowerDloadResidualNonmemory
  venomCallOracleDefs venomExecSemantics venomState venomWf ptrDiscipline list extCallOracle
  oracleExecProps lowerDloadRevertSuffix

Theorem ld_consume_call_request_growth:
  rq.cr_kind = rq'.cr_kind /\ rq.cr_value = rq'.cr_value /\
  rq.cr_target = rq'.cr_target /\ rq.cr_data = rq'.cr_data /\
  consume_call_outcome rq ro rs s = (w,r) /\
  consume_call_outcome rq' ro' rs' t = (w',r') ==>
  ((LENGTH s.vs_requests < LENGTH r.vs_requests) <=>
   (LENGTH t.vs_requests < LENGTH r'.vs_requests))
Proof
  strip_tac >> drule_all ld_computed_precompile_cong >> strip_tac >>
  gvs[consume_call_outcome_eq, record_request_def] >>
  Cases_on `computed_precompile rq'` >> simp[]
QED

Theorem dead_stor_taint_transport:
  dead_wf D /\ storage_agree_except (D.d_stor a st) st st' /\
  X SUBSET D.d_stor a st /\ Y SUBSET X ==>
  Y SUBSET D.d_stor a st'
Proof
  rw[dead_wf_def] >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem dead_trans_taint_transport:
  dead_wf D /\ storage_agree_except (D.d_trans a st) st st' /\
  X SUBSET D.d_trans a st /\ Y SUBSET X ==>
  Y SUBSET D.d_trans a st'
Proof
  rw[dead_wf_def] >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem ld_normal_call_request_backward:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  ~in_revert_forward fn s /\ MEM i.inst_opcode [CALL;STATICCALL] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' /\
  LENGTH t.vs_requests < LENGTH t'.vs_requests ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    LENGTH s.vs_requests < LENGTH s'.vs_requests
Proof
  strip_tac >>
  `inst_wf i` by (drule_all ld_annotated_inst_wf >> simp[]) >>
  `MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` by
    fs[MEM] >>
  drule_all ld_normal_external_operands >> strip_tac >>
  Cases_on `i.inst_opcode = CALL`
  >- (`?g a v off sz ro rs. i.inst_operands = [g;a;v;off;sz;ro;rs]` by
        (qpat_x_assum `inst_wf i` mp_tac >>
         simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
       drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
         ld_normal_external_input_correspondence >>
       disch_then drule >> disch_then drule >> disch_then drule >>
       qpat_assum `i.inst_opcode = CALL` (fn opc =>
         qpat_assum `i.inst_operands = _` (fn operands =>
           simp_tac (srw_ss()) [opc,operands])) >> disch_then drule >>
       simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
       qpat_x_assum `!tt ff cc. step_inst ff cc i t = OK tt ==> _`
         (drule_all_then strip_assume_tac) >>
       drule_at (Pat `step_inst _ _ _ _ = OK _`) ld_call_step_backward >>
       simp[Excl "consume_call_outcome_eq"] >>
       disch_then (qspec_then `s` mp_tac) >>
       simp[Excl "consume_call_outcome_eq"] >>
       disch_then (qspec_then `CS` strip_assume_tac) >>
       qpat_x_assum `!op. MEM op i.inst_operands /\ _ ==> _` kall_tac >>
       fs[Excl "consume_call_outcome_eq"] >>
       qpat_x_assum `_ ==> ?out w rS rT. _` mp_tac >>
       asm_rewrite_tac[] >> strip_tac >> suspend "consume_growth") >>
  `i.inst_opcode = STATICCALL` by fs[MEM] >>
  `?g a off sz ro rs. i.inst_operands = [g;a;off;sz;ro;rs]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ld_normal_external_input_correspondence >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  simp[] >> disch_then drule >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  drule_at (Pat `step_inst _ _ _ _ = OK _`) ld_call_step_backward >>
  simp[Excl "consume_call_outcome_eq"] >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[Excl "consume_call_outcome_eq"] >>
  disch_then (qspec_then `CS` strip_assume_tac) >>
  qpat_x_assum `!op. MEM op i.inst_operands /\ _ ==> _` kall_tac >>
  fs[Excl "consume_call_outcome_eq"] >>
  qpat_x_assum `_ ==> ?out w rS rT. _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >> suspend "consume_growth"
QED

Resume ld_normal_call_request_backward[consume_growth]:
  markerLib.RESUME_TAC >>
  (gvs[Excl "consume_call_outcome_eq"] >>
   `((LENGTH s.vs_requests < LENGTH rS.vs_requests) <=>
     (LENGTH t.vs_requests < LENGTH rT.vs_requests))` by
     (irule ld_consume_call_request_growth >>
      goal_assum (drule_at (Pat `consume_call_outcome _ _ _ s = _`)) >>
      goal_assum (drule_at (Pat `consume_call_outcome _ _ _ t = _`)) >>
      simp[venom_call_request_def]) >>
   gvs[update_var_def, Excl "consume_call_outcome_eq"])
QED

Finalise ld_normal_call_request_backward

Theorem ld_request_growth_external:
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]
Proof
  strip_tac >> spose_not_then assume_tac >>
  `s'.vs_requests = s.vs_requests` by
    (fs[MEM] >> drule_all step_inst_noninvoke_oracle >> simp[]) >>
  gvs[]
QED

Theorem ld_revert_interval_requests:
  lookup_block t.vs_current_bb gn.fn_blocks = SOME gb /\
  revert_forward_pair gb copypos endpos /\
  copypos <= t.vs_inst_idx /\ t.vs_inst_idx <= endpos /\
  get_instruction gb t.vs_inst_idx = SOME j /\
  step_inst fuel CT j t = OK z ==>
  z.vs_requests = t.vs_requests
Proof
  strip_tac >> Cases_on `copypos = t.vs_inst_idx`
  >- (gvs[] >> drule_all ld_revert_pair_suffix_enter >>
      simp[next_inst_def]) >>
  `copypos < t.vs_inst_idx` by decide_tac >>
  drule_all ld_revert_pair_suffix_step >>
  disch_then (qspecl_then [`ARB`, `z`, `fuel`, `CT`] mp_tac) >>
  simp[next_inst_def]
QED
