Theory readonlyInvokeCopyFwdExecutionFields
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdOpaque frameRel readonlyInvokeCopyFwdRel o1LowerDloadOccurrence o1LowerDloadRunnerBoundary
  ptrDiscipline taintAgree venomExecSemantics venomExecProps venomInstProofs1
  venomState venomInst contextCodegenRel finite_map list

Theorem ricf_fields_source_contexts[local]:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    EVERY (\f. f.cf_state.vs_call_ctx = s.vs_call_ctx) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >>
      imp_res_tac ld_step_ok_call_ctx >> gvs[])
  >- (rpt gen_tac >> strip_tac >>
      imp_res_tac ld_step_ok_call_ctx >>
      imp_res_tac ld_enters_block_call_ctx >> gvs[])
  >- (rpt gen_tac >> strip_tac >>
      imp_res_tac ld_setup_callee_call_ctx >>
      imp_res_tac ld_enters_block_call_ctx >> gvs[])
  >> rpt gen_tac >> strip_tac >>
  qspec_then `\z. z.vs_call_ctx` mp_tac bind_outputs_preserves >>
  simp[update_var_def] >> disch_then drule >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def] >> strip_tac >> gvs[]
QED

Theorem ricf_fields_frame_context[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def,
    taint_agree_def, ricf_opaque_view_def, ricf_retpc_view_def, frame_view_def,
    venom_state_component_equality]
QED

Theorem ricf_execution_stack_addresses:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt ==>
  !j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL j targets).vs_call_ctx.cc_address = t.vs_call_ctx.cc_address
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `EVERY (\f. f.cf_state.vs_call_ctx = s.vs_call_ctx) stk` by
    metis_tac[ricf_fields_source_contexts] >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G rt s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) rt maps stk targets s t` by
    fs[ricf_execution_invariant_def] >>
  `t.vs_call_ctx = s.vs_call_ctx` by metis_tac[ricf_fields_frame_context] >>
  rpt strip_tac >>
  `(EL j stk).cf_state.vs_call_ctx = s.vs_call_ctx` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `(EL j targets).vs_call_ctx = (EL j stk).cf_state.vs_call_ctx` by
    (fs[ricf_opaque_live_stack_agree_def] >>
     qpat_x_assum `!j. _ ==> ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _`
       (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
     drule ricf_fields_frame_context >> simp[merge_callee_state_def]) >>
  simp[]
QED
