Theory gasFocusLowerDloadFrameRequestRow
Ancestors o1PipelineCompose[qualified]
  lowerDloadRequestObservation lowerDloadSafetyLocations
  lowerDloadPtrCreate lowerDloadPtrCreateInterfaces
  gasFocusLowerDloadCutGuards lowerDloadPtrAggregate lowerDloadPublicTrace
  contextCodegenRel lowerDloadDefs list o1SafeUpto lowerDloadSafetyAmbient
  lowerDloadPtrPhase concretizeLayoutCutSafe ptrDiscipline pred_set
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadPtrCall venomInst
  lowerDloadOracleCallAssembly lowerDloadPtrJointScalar o1LowerDloadGhost
  concretizeLayoutLocalReturn unitShapeDefs lowerDloadPtrRel
  venomWf finite_map lowerDloadExternalBackward lowerDloadPtrCallBuffers
  lowerDloadPtrExternalCall lowerDloadPtrDelegate lowerDloadSharedState
  venomExecSemantics venomCallOracleDefs venomState

Theorem ld_external_emission_singleton[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ ld_envelope u fn s s.vs_inst_idx X p /\
  h < LENGTH X /\
  MEM (EL h X).inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  X = [inst] /\ h = 0
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
  >- (drule_all ld_envelope_supply_reserved >> strip_tac >>
      gvs[active_inst_def] >>
      `bb = bb'` by (irule ld_block_label_unique >> metis_tac[]) >>
      `EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]) X` by
        (qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
         simp[lower_dload_inst_supply_def] >>
         rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> rw[] >> gvs[]) >>
      fs[EVERY_EL] >> metis_tac[]) >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by gvs[] >>
  drule_all ld_envelope_ordinary >> strip_tac >> gvs[]
QED

Theorem ld_shared_state_at_boundary[local]:
  dload_equal_environment s t /\ dload_shared_store tn un s t ==>
  ld_shared_state tn un s t
Proof
  simp[dload_equal_environment_def, venom_state_component_equality,
       dload_shared_store_def, ld_shared_state_def, FLOOKUP_DEF] >>
  strip_tac >> rpt conj_tac
  >- (gen_tac >> first_x_assum (qspec_then `a` strip_assume_tac) >>
      irule o1PipelineComposeTheory.storage_agree_except_mono >>
      goal_assum (drule_at Any) >>
      Cases_on `a = t.vs_call_ctx.cc_address` >> simp[EMPTY_SUBSET])
  >- (gen_tac >> first_x_assum (qspec_then `a` strip_assume_tac) >>
      irule o1PipelineComposeTheory.storage_agree_except_mono >>
      goal_assum (drule_at Any) >>
      Cases_on `a = t.vs_call_ctx.cc_address` >> simp[EMPTY_SUBSET]) >>
  metis_tac[]
QED

Theorem ld_focus_frame_request_row:
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\ dead_wf D /\
  ld_sync lo P C vs stk PG G tn fn inst s t0 A frames N /\
  ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
  ld_prefix C' gn X p h t0 t /\ h < LENGTH X /\ ti = EL h X /\
  dload_boundary_core (dyn_floor C vs) lo rs
    (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) stk)
    PG PH G H0 tn un0 s t0 stk ds /\
  dload_prefix_match pfuel C' PH X h t0 H0 un0 t H un /\
  s.vs_gas_readings = t0.vs_gas_readings /\ t0.vs_gas_readings = t.vs_gas_readings /\
  gas_cut n vs t /\ active_inst gn ti t /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK t' /\ LENGTH t.vs_requests < LENGTH t'.vs_requests ==>
  un.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  un.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
    (t.vs_transient t.vs_call_ctx.cc_address)
Proof
  strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule_all ld_request_growth_external >> disch_tac >>
  qpat_x_assum `ti = EL h X` SUBST_ALL_TAC >>
  drule_all ld_external_emission_singleton >> strip_tac >>
  qpat_x_assum `X = [inst]` SUBST_ALL_TAC >>
  qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qhdtm_x_assum `dload_prefix_match`
    (strip_assume_tac o REWRITE_RULE [cj 1 dload_prefix_match_def]) >>
  qpat_x_assum `t = t0` SUBST_ALL_TAC >>
  qpat_x_assum `un = un0` SUBST_ALL_TAC >>
  rule_assum_tac (REWRITE_RULE [EL, HD]) >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  qhdtm_x_assum `o1_safe_upto`
    (strip_assume_tac o REWRITE_RULE [o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
  drule_all ptr_discipline_upto_at >> strip_tac >>
  drule_then assume_tac dload_boundary_shared_store >>
  suspend "calls"
QED

Resume ld_focus_frame_request_row[calls]:
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET] /\
   inst.inst_opcode <> RETURNDATACOPY /\ inst.inst_opcode <> REVERT` by
    (qpat_assum `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` mp_tac >>
     simp_tac bool_ss [MEM] >> strip_tac >> simp[]) >>
  `opaque_use_ok fn` by fs[fn_shape_ok_def] >>
  `!v. MEM (Var v) inst.inst_operands ==>
     v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})` by
    metis_tac[dload_original_nonopaque_operands] >>
  `!v. v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v}) ==>
     (lookup_var v s = NONE <=> lookup_var v t0 = NONE)` by
    (drule_then mp_tac dload_boundary_vars >> simp[dload_vars_match_def]) >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by fs[ld_sync_def] >>
  drule frame_reachable_prov_support >> disch_then drule >> strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (drule_then mp_tac ld_sync_ptr_ok >> simp[fn_ptr_ok_def]) >>
  `~in_revert_forward fn s` by
    (irule active_inst_not_revert_forward >> simp[fn_labels_def] >>
     qexists `inst` >> simp[]) >>
  `~about_to_revert fn inst s` by simp[about_to_revert_def] >>
  `inst_wf inst` by
    (qpat_assum `MEM inst (fn_insts fn)` mp_tac >>
     pure_rewrite_tac [fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     qpat_assum `fn_inst_wf fn` (mp_tac o REWRITE_RULE [fn_inst_wf_def]) >>
     metis_tac[]) >>
  drule_then assume_tac ld_sync_labels >>
  drule_then assume_tac dload_boundary_environment >>
  drule_then assume_tac dload_equal_environment_call_ctx >>
  drule_then assume_tac dload_equal_environment_outcomes >>
  `?s'. step_inst fuel C inst s = OK s' /\ LENGTH s.vs_requests < LENGTH s'.vs_requests` by
    suspend "backward_growth" >>
  drule_all taint_within_upto_request >> strip_tac >>
  qpat_x_assum `dload_shared_store _ _ _ _` (strip_assume_tac o REWRITE_RULE [dload_shared_store_def]) >>
  qpat_assum `!a. (_ with storage := _) = _ /\ _`
    (qspec_then `s.vs_call_ctx.cc_address` (strip_assume_tac o SIMP_RULE bool_ss [])) >>
  conj_tac
  >- (irule dead_stor_taint_transport >> simp[] >>
      qexistsl [`tn.t_stor`, `(s.vs_accounts s.vs_call_ctx.cc_address).storage`] >>
      simp[GSYM SUBSET_REFL] >> metis_tac[o1PipelineComposeTheory.storage_agree_except_mono]) >>
  irule dead_trans_taint_transport >> simp[] >>
  qexistsl [`tn.t_trans`, `s.vs_transient s.vs_call_ctx.cc_address`] >>
  simp[] >> metis_tac[o1PipelineComposeTheory.storage_agree_except_mono]
QED

Resume ld_focus_frame_request_row[backward_growth]:
  Cases_on `inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2`
  >- suspend "create" >>
  Cases_on `inst.inst_opcode = DELEGATECALL`
  >- suspend "delegate" >>
  Q.SUBGOAL_THEN `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL`
    assume_tac
  >- (qpat_assum `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` mp_tac >>
      simp_tac bool_ss [MEM] >> metis_tac[]) >>
  suspend "call_static"
QED

Resume ld_focus_frame_request_row[create]:
  `FDOM G SUBSET fn_pv P fn` by metis_tac[] >>
  `s.vs_labels = t0.vs_labels` by metis_tac[dload_equal_environment_code] >>
  `?s1. step_inst fuel C inst s = OK s1` by
    (drule_all (Q.INST [`U` |-> `set (fn_ir_vars fn) DIFF {v | retpc_var fn v}`]
                      dload_boundary_core_create) >>
     disch_then (qspec_then `C` strip_assume_tac) >> metis_tac[]) >>
  `MEM inst.inst_opcode [CREATE;CREATE2]` by fs[MEM] >>
  qexists `s1` >> simp[] >> drule_all ld_create_step_request_growth >> simp[]
QED

Resume ld_focus_frame_request_row[delegate]:
  `?g a off sz r rs'. inst.inst_operands = [g;a;off;sz;r;rs']` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  drule_all (Q.INST [`U` |-> `set (fn_ir_vars fn) DIFF {v | retpc_var fn v}`]
                    dload_delegate_evaluated_inputs) >> strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op t0 <> NONE` by
    metis_tac[dload_delegate_success_inputs] >>
  `?gv av os ot z ro rt rz.
     eval_operand g s = SOME gv /\ eval_operand g t0 = SOME gv /\
     eval_operand a s = SOME av /\ eval_operand a t0 = SOME av /\
     eval_operand off s = SOME os /\ eval_operand off t0 = SOME ot /\
     eval_operand sz s = SOME z /\ eval_operand sz t0 = SOME z /\
     eval_operand r s = SOME ro /\ eval_operand r t0 = SOME rt /\
     eval_operand rs' s = SOME rz /\ eval_operand rs' t0 = SOME rz` by
    (Cases_on `eval_operand g s` >> gvs[] >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand off s` >> gvs[] >>
     Cases_on `eval_operand off t0` >> gvs[] >>
     Cases_on `eval_operand sz s` >> gvs[] >>
     Cases_on `eval_operand r s` >> gvs[] >>
     Cases_on `eval_operand r t0` >> gvs[] >>
     Cases_on `eval_operand rs' s` >> gvs[] >> metis_tac[]) >>
  `ld_shared_state tn un0 s t0` by metis_tac[ld_shared_state_at_boundary] >>
  `read_memory (w2n os) (w2n z) s =
     read_memory (w2n ot) (w2n z) t0` by metis_tac[] >>
  drule_all ld_delegatecall_step_backward_extract >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists `update_var out w rS` >>
  simp[Excl "consume_call_outcome_eq"] >>
  `(LENGTH s.vs_requests < LENGTH rS.vs_requests) <=>
     (LENGTH t0.vs_requests < LENGTH rT.vs_requests)` by
    (irule ld_consume_call_request_growth >>
     goal_assum (drule_at (Pat `consume_call_outcome _ _ _ s = _`)) >>
     goal_assum (drule_at (Pat `consume_call_outcome _ _ _ t0 = _`)) >>
     simp[venom_call_request_def]) >>
  gvs[update_var_def, Excl "consume_call_outcome_eq"]
QED

Resume ld_focus_frame_request_row[call_static]:
  Q.SUBGOAL_THEN
    `?gas addr value a sz r rs'.
       (inst.inst_opcode = CALL /\ inst.inst_operands = [gas;addr;value;a;sz;r;rs']) \/
       (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [gas;addr;a;sz;r;rs'])`
    (REPEAT_TCL CHOOSE_THEN assume_tac)
  >- (qpat_x_assum `inst_wf inst` mp_tac >>
      qpat_assum `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL`
        strip_assume_tac >>
      simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `!v. MEM (Var v) (TL inst.inst_operands) ==>
        v IN (set (fn_ir_vars fn) DIFF {v | retpc_var fn v})` by
    (Cases_on `inst.inst_operands` >> gvs[] >> metis_tac[]) >>
  drule_all (Q.INST [`U` |-> `set (fn_ir_vars fn) DIFF {v | retpc_var fn v}`]
                    dload_call_evaluated_inputs) >> strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op t0 <> NONE` by
    (drule_at (Pat `step_inst _ _ _ _ = OK _`) dload_call_success_inputs >>
     (impl_tac >- simp[]) >> simp[]) >>
  `?gs gt av ao bo z ro rt rz.
     eval_operand gas s = SOME gs /\ eval_operand gas t0 = SOME gt /\
     eval_operand addr s = SOME av /\ eval_operand addr t0 = SOME av /\
     eval_operand a s = SOME ao /\ eval_operand a t0 = SOME bo /\
     eval_operand sz s = SOME z /\ eval_operand sz t0 = SOME z /\
     eval_operand r s = SOME ro /\ eval_operand r t0 = SOME rt /\
     eval_operand rs' s = SOME rz /\ eval_operand rs' t0 = SOME rz` by
    (qpat_assum `_ /\ inst.inst_operands = _ \/ _` strip_assume_tac >> gvs[] >>
     Cases_on `eval_operand gas s` >> gvs[] >>
     Cases_on `eval_operand gas t0` >> gvs[] >>
     Cases_on `eval_operand addr s` >> gvs[] >>
     Cases_on `eval_operand a s` >> gvs[] >>
     Cases_on `eval_operand a t0` >> gvs[] >>
     Cases_on `eval_operand sz s` >> gvs[] >>
     Cases_on `eval_operand r s` >> gvs[] >>
     Cases_on `eval_operand r t0` >> gvs[] >>
     Cases_on `eval_operand rs' s` >> gvs[] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `?vv st.
       (inst.inst_opcode = CALL /\
        inst.inst_operands = [gas;addr;value;a;sz;r;rs'] /\
        eval_operand value s = SOME vv /\ eval_operand value t0 = SOME vv /\
        (s.vs_call_ctx.cc_static ==> vv = 0w) /\ st = s.vs_call_ctx.cc_static) \/
       (inst.inst_opcode = STATICCALL /\ inst.inst_operands = [gas;addr;a;sz;r;rs'] /\
        vv = 0w /\ st = T)`
    (REPEAT_TCL CHOOSE_THEN assume_tac)
  >- (qpat_assum `_ /\ inst.inst_operands = _ \/ _` strip_assume_tac >> gvs[]
      >- (Cases_on `eval_operand value s` >> gvs[] >> metis_tac[]) >>
      metis_tac[]) >>
  `read_memory (w2n ao) (w2n z) s = read_memory (w2n bo) (w2n z) t0` by
    metis_tac[] >>
  `?s1. step_inst fuel C inst s = OK s1 /\
        exec_ext_call inst s gs av vv ao z ro rz st = OK s1 /\
        exec_ext_call inst t0 gt av vv bo z rt rz st = OK t'` by
    (drule_all (Q.INST [`value` |-> `vv`] dload_external_call_step) >>
     disch_then (qspec_then `C` strip_assume_tac) >> metis_tac[]) >>
  `computed_precompile (venom_call_request s av vv ao z st) <=>
   computed_precompile (venom_call_request t0 av vv bo z st)` by
    (irule lowerDloadOracleSelectionTheory.ld_computed_precompile_cong >>
     simp[venom_call_request_def]) >>
  drule_then assume_tac concretizeLayoutExternalCallTheory.ext_call_execution_request_growth >>
  qpat_assum `exec_ext_call _ s _ _ _ _ _ _ _ _ = _`
    (mp_then Any assume_tac concretizeLayoutExternalCallTheory.ext_call_execution_request_growth) >>
  qexists `s1` >> metis_tac[]
QED

Finalise ld_focus_frame_request_row
