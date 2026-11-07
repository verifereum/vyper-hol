Theory lowerDloadExternalData
Ancestors
  lowerDloadExternalInputs lowerDloadExternalEffects lowerDloadExternalMemory
  lowerDloadExternalBackward lowerDloadNormalData lowerDloadReachableDiscipline
  lowerDloadOwnership lowerDloadCoverageInvariant lowerDloadPairedBoundary
  lowerDloadFrameCertificate lowerDloadVariableTransport lowerDloadMaskBounds
  lowerDloadResidualNonmemory lowerDloadExternalReconstruct lowerDloadSharedState
  venomWf venomCallOracleDefs
  memLocDefs ptrDiscipline o1PassContract venomInst venomState venomExecSemantics
  codegenRel contextCodegenRel list finite_map pred_set words

Theorem ld_normal_external_backward:
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
  ~in_revert_forward fn s /\
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
      astk live keys d A suspended gstk f
Proof
  strip_tac >>
  `inst_wf i` by (drule_all ld_annotated_inst_wf >> simp[]) >>
  drule_all ld_normal_external_operands >> strip_tac >>
  Cases_on `i.inst_opcode = CALL`
  >- ( `?g a v off sz ro rs. i.inst_operands = [g;a;v;off;sz;ro;rs]` by
        (qpat_x_assum `inst_wf i` mp_tac >>
         simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
       drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
         ld_normal_external_input_correspondence >>
       disch_then drule >> disch_then drule >> disch_then drule >>
       simp[] >>
       disch_then drule >>
       simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
       drule_at (Pat `step_inst _ _ _ _ = OK _`) ld_call_step_backward >>
       simp[Excl "consume_call_outcome_eq"] >>
       disch_then (qspec_then `s` mp_tac) >>
       simp[Excl "consume_call_outcome_eq"] >>
       disch_then (qspec_then `CS` strip_assume_tac) >>
       qpat_x_assum `!op. MEM op i.inst_operands /\ _ ==> _` kall_tac >>
       fs[Excl "consume_call_outcome_eq"] >>
       qpat_x_assum `_ ==> ?out w rS rT. _` mp_tac >>
       asm_rewrite_tac[] >> strip_tac >>
       suspend "call_shared") >>
  Cases_on `i.inst_opcode = STATICCALL`
  >- (`?g a off sz ro rs. i.inst_operands = [g;a;off;sz;ro;rs]` by
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
       asm_rewrite_tac[] >> strip_tac >> suspend "call_shared") >>
  Cases_on `i.inst_opcode = DELEGATECALL`
  >- (`?g a off sz ro rs. i.inst_operands = [g;a;off;sz;ro;rs]` by
        (qpat_x_assum `inst_wf i` mp_tac >>
         simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
       drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
         ld_normal_external_input_correspondence >>
       disch_then drule >> disch_then drule >> disch_then drule >>
       simp[] >> disch_then drule >>
       simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
       drule_at (Pat `step_inst _ _ _ _ = OK _`) ld_delegatecall_step_backward_extract >>
       simp[] >>
       disch_then (qspecl_then [`un`,`tn`,`s`] mp_tac) >>
       qpat_x_assum `!op. MEM op i.inst_operands /\ _ ==> _` kall_tac >>
       fs[] >>
       disch_then (qspec_then `CS` strip_assume_tac) >>
       qpat_x_assum `_ ==> ?out w rS rT v rr. _` mp_tac >>
       gvs[] >> strip_tac >> suspend "delegate_shared") >>
  Cases_on `i.inst_opcode = CREATE`
  >- (`?v off sz. i.inst_operands = [v;off;sz]` by
        (qpat_x_assum `inst_wf i` mp_tac >>
         simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
       drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
         ld_normal_external_input_correspondence >>
       disch_then drule >> disch_then drule >> disch_then drule >>
       simp[] >> disch_then drule >>
       simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
       drule_at (Pat `step_inst _ _ _ _ = OK _`) ld_create_step_backward >>
       simp[Excl "consume_create_outcome_eq"] >>
       disch_then (qspec_then `s` mp_tac) >>
       qpat_x_assum `!op. MEM op i.inst_operands /\ _ ==> _` kall_tac >>
       fs[Excl "consume_create_outcome_eq"] >>
       disch_then (qspec_then `CS` strip_assume_tac) >>
       qpat_x_assum `_ ==> ?out w rS rT. _` mp_tac >>
       gvs[Excl "consume_create_outcome_eq"] >> strip_tac >> suspend "create_shared") >>
  `i.inst_opcode = CREATE2` by fs[MEM] >>
  `?v off sz salt. i.inst_operands = [v;off;sz;salt]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ld_normal_external_input_correspondence >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  simp[] >> disch_then drule >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  drule_at (Pat `step_inst _ _ _ _ = OK _`) ld_create_step_backward >>
  simp[Excl "consume_create_outcome_eq"] >>
  disch_then (qspec_then `s` mp_tac) >>
  qpat_x_assum `!op. MEM op i.inst_operands /\ _ ==> _` kall_tac >>
  fs[Excl "consume_create_outcome_eq"] >>
  disch_then (qspec_then `CS` strip_assume_tac) >>
  qpat_x_assum `_ ==> ?out w rS rT. _` mp_tac >>
  gvs[Excl "consume_create_outcome_eq"] >> strip_tac >> suspend "create_shared"
QED

Resume ld_normal_external_backward[call_shared]:
  markerLib.RESUME_TAC >> (
       `ld_shared_state (step_taint i s rS tn) (step_taint i t rT un) rS rT` by
         (irule ld_call_consume_tainted_shared >>
          goal_assum (drule_at Any) >>
          reverse conj_tac >- simp[MEM] >>
          goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >>
          simp[MEM, venom_call_request_def, Excl "consume_call_outcome_eq"] >>
          qpat_x_assum `read_memory _ _ s = _` mp_tac >>
          asm_rewrite_tac[]) >>
       drule ld_consume_call_frame_fields >> strip_tac >>
       rev_drule ld_consume_call_frame_fields >> strip_tac >>
       drule ld_external_bind_tainted_shared >> strip_tac >>
       qexists_tac `update_var out w rS` >>
       conj_tac >- asm_rewrite_tac[] >>
       `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
          (step_taint i s rS tn).t_mem (step_taint i t rT un).t_mem
          (\a. read_memory a 1 rS) (\b. read_memory b 1 rT)` by
         (drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
            ld_external_memory_preserved >>
          disch_then drule >> disch_then drule >>
          simp[MEM] >>
          disch_then (qspecl_then [`rT`,`rS`] mp_tac) >>
          simp[mem_write_ops_def, source_memory_write_ranges_def,
               Excl "consume_call_outcome_eq"] >>
          disch_then irule >>
          qpat_x_assum `!v'. _ ==> v' IN U` mp_tac >>
          simp[] >> metis_tac[]) >>
       drule ld_normal_data_companions >> strip_tac >>
       drule ld_normal_data_frame >> disch_tac >>
       drule ld_frame_data_shared >> disch_tac >>
       `(!a. a <> rS.vs_call_ctx.cc_address ==>
          (rS.vs_accounts a).storage = (rT.vs_accounts a).storage) /\
        (!a. a <> rS.vs_call_ctx.cc_address ==>
          rS.vs_transient a = rT.vs_transient a)` by
         (irule ld_external_consume_noncurrent >>
          goal_assum (drule_at Any) >>
          pure_rewrite_tac [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR] >>
          simp[NoAsms, EXISTS_OR_THM, Excl "consume_call_outcome_eq",
               Excl "consume_create_outcome_eq"] >>
          disj1_tac >>
          goal_assum (drule_at (Pat `consume_call_outcome _ _ _ _ = _`)) >>
          goal_assum (drule_at (Pat `consume_call_outcome _ _ _ _ = _`)) >>
          simp[venom_call_request_def, Excl "consume_call_outcome_eq"] >>
          qpat_x_assum `read_memory _ _ s = _` mp_tac >>
          asm_rewrite_tac[]) >>
       drule ld_consume_call_vars >> disch_tac >>
       rev_drule ld_consume_call_vars >> disch_tac >>
       drule ld_consume_call_labels >> disch_tac >>
       rev_drule ld_consume_call_labels >> disch_tac >>
       qpat_assum `!w out. ld_shared_state _ _ _ _`
         (qspecl_then [`w`,`out`] assume_tac) >>
       drule ld_shared_state_masks >> strip_tac >>
       drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
         ld_external_normal_reconstruct >>
       asm_rewrite_tac[] >> disch_then irule >>
       simp[MEM, update_var_def] >>
       conj_tac
       >- (qexistsl_tac [`rS`,`rT`,`w`] >> simp[update_var_def]) >>
       qpat_x_assum `ld_byte_rel _ _ _ _ _` mp_tac >>
       simp[step_taint_def, update_var_def, mem_taint_def, new_site_bytes_def,
            step_writes_def, read_memory_def])
QED

Resume ld_normal_external_backward[delegate_shared]:
  drule_all ld_delegate_extract_tainted_shared >> strip_tac >>
  drule ld_extract_result_frame_fields >> strip_tac >>
  rev_drule ld_extract_result_frame_fields >> strip_tac >>
  drule ld_extract_result_vars >> disch_tac >>
  rev_drule ld_extract_result_vars >> disch_tac >>
  drule ld_extract_result_labels >> disch_tac >>
  rev_drule ld_extract_result_labels >> disch_tac >>
  drule ld_external_bind_tainted_shared >> strip_tac >>
  qexists_tac `update_var out w rS` >>
  conj_tac >- asm_rewrite_tac[] >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
     (step_taint i s rS tn).t_mem (step_taint i t rT un).t_mem
     (\a. read_memory a 1 rS) (\b. read_memory b 1 rT)` by
    (drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       ld_external_memory_preserved >>
     disch_then drule >> disch_then drule >> simp[MEM] >>
     disch_then (qspecl_then [`rT`,`rS`] mp_tac) >>
     simp[mem_write_ops_def, source_memory_write_ranges_def] >>
     disch_then irule >>
     qpat_x_assum `!v'. _ ==> v' IN U` mp_tac >> simp[] >> metis_tac[]) >>
  qpat_assum `!w out. ld_shared_state _ _ _ _`
    (qspecl_then [`w`,`out`] assume_tac) >>
  drule ld_shared_state_masks >> strip_tac >>
  drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ld_external_normal_reconstruct >>
  asm_rewrite_tac[] >> disch_then irule >>
  simp[MEM, update_var_def] >>
  conj_tac
  >- (qexistsl_tac [`rS`,`rT`,`w`] >> simp[update_var_def]) >>
  qpat_x_assum `ld_byte_rel _ _ _ _ _` mp_tac >>
  simp[step_taint_def, update_var_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, read_memory_def]
QED

Resume ld_normal_external_backward[create_shared]:
  markerLib.RESUME_TAC >> (
  `ld_shared_state (step_taint i s rS tn) (step_taint i t rT un) rS rT` by
    (irule ld_create_consume_tainted_shared >>
     goal_assum (drule_at Any) >>
     reverse conj_tac >- simp[MEM] >>
     goal_assum (drule_at (Pat `consume_create_outcome _ _ = _`)) >>
     goal_assum (drule_at (Pat `consume_create_outcome _ _ = _`)) >>
     simp[MEM, venom_create_request_def, Excl "consume_create_outcome_eq"]) >>
  drule ld_consume_create_frame_fields >> strip_tac >>
  rev_drule ld_consume_create_frame_fields >> strip_tac >>
  drule ld_consume_create_vars >> disch_tac >>
  rev_drule ld_consume_create_vars >> disch_tac >>
  drule ld_consume_create_labels >> disch_tac >>
  rev_drule ld_consume_create_labels >> disch_tac >>
  drule ld_external_bind_tainted_shared >> strip_tac >>
  qexists_tac `update_var out w rS` >>
  conj_tac >- asm_rewrite_tac[] >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
     (step_taint i s rS tn).t_mem (step_taint i t rT un).t_mem
     (\a. read_memory a 1 rS) (\b. read_memory b 1 rT)` by
    (drule ld_normal_data_memory >> disch_tac >>
     irule ld_create_memory_preserved >>
     goal_assum (drule_at Any) >> simp[MEM]) >>
  drule ld_normal_data_companions >> strip_tac >>
  drule ld_normal_data_frame >> disch_tac >>
  drule ld_frame_data_shared >> disch_tac >>
  `(!a. a <> rS.vs_call_ctx.cc_address ==>
     (rS.vs_accounts a).storage = (rT.vs_accounts a).storage) /\
   (!a. a <> rS.vs_call_ctx.cc_address ==>
     rS.vs_transient a = rT.vs_transient a)` by
    (irule ld_external_consume_noncurrent >>
     goal_assum (drule_at Any) >>
     pure_rewrite_tac [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR] >>
     simp[NoAsms, EXISTS_OR_THM, Excl "consume_call_outcome_eq",
          Excl "consume_create_outcome_eq"] >> disj2_tac >>
     goal_assum (drule_at (Pat `consume_create_outcome _ _ = _`)) >>
     goal_assum (drule_at (Pat `consume_create_outcome _ _ = _`)) >>
     simp[venom_create_request_def, Excl "consume_create_outcome_eq"]) >>
  qpat_assum `!w out. ld_shared_state _ _ _ _`
    (qspecl_then [`w`,`out`] assume_tac) >>
  drule ld_shared_state_masks >> strip_tac >>
  drule_at (Pat `ld_normal_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ld_external_normal_reconstruct >>
  asm_rewrite_tac[] >> disch_then irule >>
  simp[MEM, update_var_def] >>
  conj_tac
  >- (qexistsl_tac [`rS`,`rT`,`w`] >> simp[update_var_def]) >>
  qpat_x_assum `ld_byte_rel _ _ _ _ _` mp_tac >>
  simp[step_taint_def, update_var_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, read_memory_def])
QED

Finalise ld_normal_external_backward
