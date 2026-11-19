Theory requestCutReplayProofs
Ancestors
  e2eRequestCutDefs jointRequestCut o1RequestContract contextRawReachable
  frameRawProjection frameJointTrace stepWriteFootprintBase
  concretizePtrOrdinaryNext concretizePtrCoverageStaticMemReachability
  frameAllocationOwnership venomExecProofs venomInstProofs venomInst
  venomWf venomState list rich_list arithmetic
  o1CodeEndConcretizeObservation o1PassContract unitLabelMapIdentity
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrRequestHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrDeletedGapHistory
  concretizePtrSourceOwnership concretizeMemLocDefs codegenSymRel
  concretizePtrTaintContent concretizePtrOpaqueRetpc concretizePtrSharedFields
  concretizeLayoutSupplement concretizeLayoutExternalRequests ptrDiscipline vfmState
  finite_map pred_set
  o1CodeEndSueTransport o1ContractSue singleUseExpansionSupplySim
  o1PassLift o1FrameLockstep venomPassSchedule stateFrame option
  lowerDloadPtrCall lowerDloadSafetyKernel o1LowerDloadShared fmpStageRel
  venomCallOracleDefs requestCutClippedPipeline venomExecProps venomExecSemantics
  extCallOracle lowerDloadNormalData lowerDloadCoverageInvariant lowerDloadSharedState
Libs
  stepInstBaseLib

Theorem ctx_rq_upto_from_endpoints:
  EVERY wf_function C'.ctx_functions /\
  raw_reachable vs C fn inst s /\ raw_reachable vs' C' fn' inst' t /\
  k < LENGTH s.vs_requests /\ k < LENGTH t.vs_requests /\
  LIST_REL (request_agree_except D)
    (TAKE (SUC k) s.vs_requests) (TAKE (SUC k) t.vs_requests) ==>
  ctx_rq_upto D k C C' vs vs'
Proof
  strip_tac >> simp[ctx_rq_upto_def] >>
  qx_genl_tac [`g`, `j`, `u`, `i`] >> strip_tac >>
  qexistsl_tac [`fn`, `inst`, `s`] >> simp[] >>
  `i < LENGTH s.vs_requests /\ i < LENGTH t.vs_requests` by decide_tac >>
  `EL i u.vs_requests = EL i t.vs_requests` by
    (mp_tac (Q.INST [`C` |-> `C'`, `vs0` |-> `vs'`,
                     `fn` |-> `fn'`, `inst` |-> `inst'`, `s` |-> `t`,
                     `fn'` |-> `g`, `inst'` |-> `j`, `t` |-> `u`]
                     raw_reachable_requests_comparable) >>
     simp[] >> rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     gvs[EL_APPEND1]) >>
  `SUC k <= LENGTH s.vs_requests /\ SUC k <= LENGTH t.vs_requests` by decide_tac >>
  fs[LIST_REL_EL_EQN, LENGTH_TAKE_EQ] >>
  qpat_x_assum `!n. n < SUC k ==> _` (qspec_then `i` mp_tac) >>
  simp[EL_TAKE]
QED

(* After an external operation returns OK, its post-step request list is
   present at the next instruction of that block. *)
Theorem raw_reachable_recording_successor[local]:
  EVERY wf_function C.ctx_functions /\
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK u /\ LENGTH s.vs_requests < LENGTH u.vs_requests ==>
  ?next. raw_reachable vs C fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (qpat_assum `raw_reachable vs C fn inst s`
        (mp_tac o MATCH_MP ptr_raw_reachable_frame) >>
     metis_tac[frame_reachable_functions_member]) >>
  `EVERY bb_well_formed fn.fn_blocks` by
    (fs[EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `~is_terminator inst.inst_opcode` by
    (drule_all step_inst_request_outcomes >> strip_tac >> fs[is_terminator_def]) >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `active_inst fn inst s` by metis_tac[raw_reachable_active] >>
  drule_all ptr_ordinary_next_active >> strip_tac >>
  qexists_tac `i` >> irule raw_reachable_next >> metis_tac[]
QED

Theorem request_cut_paired_recordings:
  EVERY wf_function C.ctx_functions /\ EVERY wf_function C'.ctx_functions /\
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
  LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK u /\
  k < LENGTH u.vs_requests /\
  raw_reachable vs' C' fn' inst' t /\ inst'.inst_opcode <> INVOKE /\
  LENGTH t.vs_requests = k /\ step_inst fuel' C' inst' t = OK v /\
  k < LENGTH v.vs_requests /\
  LIST_REL (request_agree_except D) u.vs_requests v.vs_requests ==>
  request_agree_except D (EL k u.vs_requests) (EL k v.vs_requests) /\
  ctx_rq_upto D k C C' vs vs'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- fs[LIST_REL_EL_EQN] >>
  `LENGTH s.vs_requests < LENGTH u.vs_requests /\ LENGTH t.vs_requests < LENGTH v.vs_requests` by simp[] >>
  mp_tac (Q.INST [`C` |-> `C`, `vs` |-> `vs`, `fn` |-> `fn`,
    `inst` |-> `inst`, `s` |-> `s`, `fuel` |-> `fuel`, `u` |-> `u`]
    raw_reachable_recording_successor) >>
  asm_rewrite_tac[] >> disch_then (qx_choose_then `next` assume_tac) >>
  mp_tac (Q.INST [`C` |-> `C'`, `vs` |-> `vs'`, `fn` |-> `fn'`,
    `inst` |-> `inst'`, `s` |-> `t`, `fuel` |-> `fuel'`, `u` |-> `v`]
    raw_reachable_recording_successor) >>
  asm_rewrite_tac[] >> disch_then (qx_choose_then `next'` assume_tac) >>
  irule ctx_rq_upto_from_endpoints >> simp[] >>
  qexistsl_tac [`fn`, `fn'`, `next`, `next'`, `u with vs_inst_idx := SUC s.vs_inst_idx`,
    `v with vs_inst_idx := SUC t.vs_inst_idx`] >> simp[] >>
  `SUC k <= LENGTH u.vs_requests /\ SUC k <= LENGTH v.vs_requests` by decide_tac >>
  fs[LIST_REL_EL_EQN, LENGTH_TAKE_EQ, EL_TAKE]
QED

Theorem request_cut_paired_endpoints:
  EVERY wf_function C.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
  LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK u /\
  k < LENGTH u.vs_requests /\
  joint_trace vs0 ctx q0 es qs
    (JointConfig stk PG G tn endfn endinst t oms om hs h) /\
  LENGTH vs0.vs_requests <= k /\ k < LENGTH t.vs_requests /\
  LIST_REL (request_agree_except D)
    (TAKE (SUC k) u.vs_requests) (TAKE (SUC k) t.vs_requests) ==>
  (?fn' inst' s' fuel' u'.
    raw_reachable vs0 ctx fn' inst' s' /\ inst'.inst_opcode <> INVOKE /\
    LENGTH s'.vs_requests = k /\ step_inst fuel' ctx inst' s' = OK u' /\
    k < LENGTH u'.vs_requests /\
    request_agree_except D (EL k u.vs_requests) (EL k u'.vs_requests)) /\
  ctx_rq_upto D k C ctx vs vs0
Proof
  strip_tac >> conj_tac
  >- (drule_all joint_trace_request_crossing >> strip_tac >>
      qexistsl_tac [`fn0`, `inst0`, `s'`, `fuel'`, `post`] >> simp[] >>
      `SUC k <= LENGTH u.vs_requests /\ SUC k <= LENGTH t.vs_requests` by decide_tac >>
      `request_agree_except D (EL k u.vs_requests) (EL k t.vs_requests)` by
        (fs[LIST_REL_EL_EQN, LENGTH_TAKE_EQ] >>
         qpat_x_assum `!n. n < SUC k ==> _` (qspec_then `k` mp_tac) >>
         simp[EL_TAKE]) >>
      fs[IS_PREFIX_APPEND] >>
      qpat_x_assum `t.vs_requests = _` SUBST_ALL_TAC >> gvs[EL_APPEND1]) >>
  `LENGTH s.vs_requests < LENGTH u.vs_requests` by simp[] >>
  drule_all raw_reachable_recording_successor >> strip_tac >>
  drule joint_trace_reachable >> strip_tac >>
  drule_all joint_config_raw >> strip_tac >>
  irule ctx_rq_upto_from_endpoints >> simp[] >>
  qexistsl_tac [`fn`, `endfn`, `next`, `endinst`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`, `t`] >> simp[]
QED

(* Use the stopped trace itself. Any proper pre-cut terminal still has an
   outcome, because the same initial oracle serves the raw recording step. *)
Theorem request_cut_stopped_trace_crossed:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  raw_variant fmp vs vs0 /\ EVERY wf_function C.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
  LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK u /\
  k < LENGTH u.vs_requests /\
  joint_trace vs0 ctx q0 es qs
    (JointConfig stk PG G tn endfn endinst t oms om hs h) /\
  (request_cut k t ==> t.vs_outcomes = []) ==>
  vs.vs_outcomes = vs0.vs_outcomes /\ vs.vs_requests = vs0.vs_requests /\
  LENGTH vs0.vs_requests <= k /\ k < LENGTH t.vs_requests
Proof
  strip_tac >>
  `vs.vs_outcomes = vs0.vs_outcomes /\ vs.vs_requests = vs0.vs_requests` by
    (qpat_x_assum `raw_variant fmp vs vs0` mp_tac >>
     pure_rewrite_tac[raw_variant_def, gas_variant_def] >>
     disch_then (mp_tac o Q.AP_TERM `\v. (v.vs_outcomes,v.vs_requests)`) >> simp[]) >>
  `LENGTH vs0.vs_requests <= k` by
    (drule_all raw_reachable_recorded_oracle_drop >> simp[]) >>
  `LENGTH s.vs_requests < LENGTH u.vs_requests` by simp[] >>
  `s.vs_outcomes <> []` by metis_tac[recording_step_has_outcome] >>
  `raw_reachable vs0 ctx endfn endinst t` by
    (drule joint_trace_reachable >> strip_tac >> drule_all joint_config_raw >> simp[]) >>
  `k < LENGTH t.vs_requests` by
    (spose_not_then assume_tac >>
     `LENGTH t.vs_requests <= LENGTH s.vs_requests` by decide_tac >>
     `t.vs_outcomes <> []` by metis_tac[earlier_recorded_index_has_outcome] >>
     fs[request_cut_def]) >>
  simp[]
QED

Theorem paired_history_supplement[local]:
  ptr_history_content tn s t ==>
  concretize_supplement D tn (s with vs_requests := t.vs_requests) t
Proof
  strip_tac >>
  `LIST_REL (request_agree_except D) t.vs_requests t.vs_requests` by
    (irule EVERY2_refl >> simp[request_agree_except_refl]) >>
  fs[ptr_history_content_def, ptr_taint_content_def,
     ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def] >>
  fs[concretize_supplement_def, accounts_agree_except_def,
     transient_agree_except_def, imms_agree_except_def, contract_storage_def,
     vfmStateTheory.lookup_account_def, contract_transient_def] >>
  qpat_x_assum `s.vs_call_ctx = t.vs_call_ctx` (fn eq =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >> PURE_REWRITE_TAC [eq]) >>
  rpt conj_tac
  >- (gen_tac >> Cases_on `a = t.vs_call_ctx.cc_address` >>
      fs[storage_agree_except_def, word_agree_except_def])
  >- (gen_tac >> Cases_on `a = t.vs_call_ctx.cc_address` >>
      fs[storage_agree_except_def, word_agree_except_def]) >>
  fs[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem sue_frame_recording_step[local]:
  ctx_bisim C C' /\ fn_inst_wf f /\ EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts f) /\
  sue_frame_align C C' f g entry j t /\
  j.inst_opcode <> INVOKE /\ step_inst fuel C' j t = OK v /\
  LENGTH t.vs_requests < LENGTH v.vs_requests ==>
  ?i s m u. frame_reach C f entry i s /\ i.inst_opcode = j.inst_opcode /\
    step_inst m C i s = OK u /\ s.vs_requests = t.vs_requests /\
    s.vs_outcomes = t.vs_outcomes /\ u.vs_requests = v.vs_requests
Proof
  strip_tac >> drule_all step_inst_request_outcomes >> strip_tac >>
  `j.inst_opcode <> ASSIGN` by fs[MEM] >>
  qpat_x_assum `sue_frame_align _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [sue_frame_align_def]) >>
  `MEM bb f.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!x. MEM (Var x) (EL i bb.bb_instructions).inst_operands ==>
    MEM x (fn_ir_vars f)` by metis_tac[sue_original_operand_covered, MEM_EL] >>
  drule_all sue_segments_supply_index_ready >> strip_tac >>
  drule_all sue_segment_operand_eval >> strip_tac >>
  `EL j' (EL i segs) = LAST (EL i segs)` by metis_tac[] >>
  drule_all sue_expand_inst_supply_segment >>
  disch_then (qx_choosel_then [`copies`, `operands`] strip_assume_tac) >>
  `j' = LENGTH copies` by
    (`j' < SUC (LENGTH copies)` by fs[] >>
     Cases_on `j' < LENGTH copies`
     >- (`(EL j' copies).inst_opcode = ASSIGN` by fs[EVERY_EL] >>
         fs[EL_APPEND1]) >>
     decide_tac) >>
  `j' = LENGTH (BUTLAST (EL i segs))` by simp[FRONT_APPEND_NOT_NIL] >>
  `run_insts 0 C' (BUTLAST (EL i segs)) b = OK (sue_idx0 t)` by
    fs[FRONT_APPEND_NOT_NIL, TAKE_LENGTH_ID] >>
  `step_inst fuel C' (LAST (EL i segs)) t = OK v` by metis_tac[] >>
  drule_all sue_segment_final_ok_back >> strip_tac >>
  fs[sue_state_rel_def] >>
  imp_res_tac execution_frame_fields >>
  qexistsl_tac [`EL i bb.bb_instructions`, `u`, `fuel0`, `w`] >> simp[]
QED

Theorem sue_stage_recording_step:
  ctx_pass_stage rp (CFP_Simple VP_SingleUseExpansion) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY (o1_fn_row 6) C.ctx_functions /\ vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  raw_reachable vs C' f j t /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK v /\ LENGTH t.vs_requests < LENGTH v.vs_requests ==>
  ?g i s m u. raw_reachable vs C g i s /\ i.inst_opcode = j.inst_opcode /\
    step_inst m C i s = OK u /\ s.vs_requests = t.vs_requests /\
    s.vs_outcomes = t.vs_outcomes /\ u.vs_requests = v.vs_requests
Proof
  strip_tac >>
  `ctx_bisim C C'` by metis_tac[sue_stage_bisim] >>
  drule_all sue_code_end_stage_pairs >>
  disch_then (qspec_then `vs.vs_labels` assume_tac) >>
  `frame_origin vs C C' f j t` by
    (irule frame_sim_raw_origins >> simp[] >>
     fs[ctx_pass_stage_def] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >>
  disch_then (qx_choosel_then [`g`, `entry`] strip_assume_tac) >>
  rename1 `lookup_function source_name C.ctx_functions = SOME g` >>
  drule list_rel_lookup_function >> simp[] >>
  disch_then (qspec_then `source_name` mp_tac) >> simp[OPTREL_def] >>
  strip_tac >>
  `sue_frame_align C C' g f entry j t` by
    (irule sue_frame_reach_align >> metis_tac[]) >>
  drule_all sue_frame_recording_step >>
  disch_then (qx_choosel_then [`i`, `s`, `m`, `u`] strip_assume_tac) >>
  qexistsl_tac [`g`, `i`, `s`, `m`, `u`] >>
  simp[] >> metis_tac[frame_reach_raw_reachable]
QED

(* The current store mask at a relocated request is independent of the
   mask used for its earlier request history. *)
Theorem relocated_snapshot_agrees:
  dload_shared_store tn un s t /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  rq.cr_accounts = s.vs_accounts /\ rq'.cr_accounts = t.vs_accounts /\
  rq.cr_tStorage = s.vs_transient /\ rq'.cr_tStorage = t.vs_transient /\
  ptr_request_shell rq rq' ==>
  request_agree_except D rq rq'
Proof
  strip_tac >>
  fs[request_agree_except_def, ptr_request_shell_def, accounts_agree_except_def,
     transient_agree_except_def, dload_shared_store_def, storage_agree_except_def,
     word_agree_except_def, key_taint_def, SUBSET_DEF] >>
  conj_tac >> qx_genl_tac [`a`, `key`, `byte`] >> strip_tac >>
  qpat_x_assum `!a. (s.vs_accounts a with storage := _) = _ /\ _`
    (qspec_then `a` strip_assume_tac) >>
  Cases_on `a = s.vs_call_ctx.cc_address` >> fs[] >> metis_tac[]
QED

Theorem fmp_stage_rel_shared_store:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  dload_shared_store tn tn s t
Proof
  simp[fmp_stage_rel_def, ld_shared_agree_def, dload_shared_store_def,
       storage_agree_except_def, key_taint_def, word_agree_except_def] >>
  rpt strip_tac >>
  fs[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_clipped_normal_shared_store:
  ld_normal_data C fn V U lo E L H AP BP AG BH tn un
    (s with vs_outcomes := os) (t with vs_outcomes := ot)
    astk live keys d A suspended gstk f ==>
  dload_shared_store tn tn s t
Proof
  simp[ld_normal_data_def, ld_frame_data_def, ld_shared_state_def,
       dload_shared_store_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> simp[] >> conj_tac
  >- (gen_tac >> Cases_on `a = s.vs_call_ctx.cc_address` >>
      fs[storage_agree_except_def, word_agree_except_def] >> metis_tac[]) >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

(* Pointer relocation may change both buffer offsets. The request sees the
   input bytes and scalar arguments, and never observes the return buffer. *)
Theorem request_step_relocated_shell:
  ((inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;off;sz;ro;rs] /\
      scalars = [g;a;v;sz]) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\
      inst.inst_operands = [g;a;off;sz;ro;rs] /\ scalars = [g;a;sz]) \/
   (inst.inst_opcode = CREATE /\ inst.inst_operands = [v;off;sz] /\
      scalars = [v;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [v;off;sz;salt] /\
      scalars = [v;sz;salt])) /\
  (!op. MEM op scalars ==> eval_operand op s = eval_operand op t) /\
  eval_operand off s = SOME p /\ eval_operand off t = SOME q /\
  eval_operand sz s = SOME n /\
  read_memory (w2n p) (w2n n) s = read_memory (w2n q) (w2n n) t /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  step_inst fuel C inst s = OK u /\ step_inst fuel' C' inst t = OK u' ==>
  ptr_request_shell (LAST u.vs_requests) (LAST u'.vs_requests)
Proof
  strip_tac >> fs[MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `inst.inst_opcode` >> gvs[step_inst_non_invoke] >>
  with_opcode_clause gvs >> gvs[eval_operands_def, AllCaseEqs()] >>
  Cases_on `inst.inst_outputs` >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def] >>
  rename1 `out::outs` >> Cases_on `outs` >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
      AllCaseEqs(), update_var_def, record_request_def, LAST_APPEND] >>
  simp[ptr_request_shell_def, venom_call_request_def, venom_create_request_def]
QED

Theorem request_step_relocated_backward:
  ((inst.inst_opcode = CALL /\ inst.inst_operands = [g;a;v;off;sz;ro;rs] /\
      scalars = [g;a;v;sz]) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\
      inst.inst_operands = [g;a;off;sz;ro;rs] /\ scalars = [g;a;sz]) \/
   (inst.inst_opcode = CREATE /\ inst.inst_operands = [v;off;sz] /\
      scalars = [v;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [v;off;sz;salt] /\
      scalars = [v;sz;salt])) /\
  (!op. MEM op scalars ==> eval_operand op s = eval_operand op t) /\
  (!op. MEM op inst.inst_operands ==> ?w. eval_operand op s = SOME w) /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  s.vs_outcomes = t.vs_outcomes /\ step_inst fuel CT inst t = OK t' ==>
  ?s'. step_inst fuel CS inst s = OK s'
Proof
  strip_tac >> fs[MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `inst.inst_opcode` >> gvs[step_inst_non_invoke] >>
  qpat_x_assum `!op. _ ==> ?w. eval_operand op s = SOME w`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]) >>
  with_opcode_clause gvs >> gvs[eval_operands_def, AllCaseEqs()] >>
  Cases_on `inst.inst_outputs` >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def] >>
  rename1 `out::outs` >> Cases_on `outs` >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def, AllCaseEqs()]
QED

Theorem relocated_request_agrees:
  dload_shared_store tn un s t /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  LENGTH s.vs_requests = k /\ LENGTH t.vs_requests = k /\
  inst.inst_opcode <> INVOKE /\ inst'.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK u /\ step_inst fuel' C' inst' t = OK v /\
  k < LENGTH u.vs_requests /\ k < LENGTH v.vs_requests /\
  ptr_request_shell (LAST u.vs_requests) (LAST v.vs_requests) ==>
  request_agree_except D (EL k u.vs_requests) (EL k v.vs_requests)
Proof
  strip_tac >>
  `LENGTH s.vs_requests < LENGTH u.vs_requests /\
   LENGTH t.vs_requests < LENGTH v.vs_requests` by simp[] >>
  `?rq. u.vs_requests = s.vs_requests ++ [rq] /\
    rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient` by
    metis_tac[recording_step_appends_one] >>
  `?rq'. v.vs_requests = t.vs_requests ++ [rq'] /\
    rq'.cr_accounts = t.vs_accounts /\ rq'.cr_tStorage = t.vs_transient` by
    metis_tac[recording_step_appends_one] >>
  fs[EL_APPEND2,LAST_APPEND] >>
  irule relocated_snapshot_agrees >> simp[] >> qexistsl_tac [`s`,`t`,`tn`,`un`] >> simp[]
QED

Theorem request_cut_compose_history:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  EVERY wf_function C.ctx_functions /\ EVERY wf_function C'.ctx_functions /\
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C.ctx_functions /\
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C'.ctx_functions /\
  ctx_abort_rq D C C'
    (vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes)
    (vt with vs_outcomes := TAKE (k - LENGTH vt.vs_requests) vt.vs_outcomes) /\
  raw_reachable vs C fn inst s /\ raw_reachable vt C' fn' inst' t /\
  LENGTH s.vs_requests = k /\ LENGTH t.vs_requests = k /\
  inst.inst_opcode <> INVOKE /\ inst'.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK u /\ step_inst fuel' C' inst' t = OK v /\
  k < LENGTH u.vs_requests /\ k < LENGTH v.vs_requests /\
  request_agree_except D (EL k u.vs_requests) (EL k v.vs_requests) ==>
  LIST_REL (request_agree_except D) u.vs_requests v.vs_requests /\
  ctx_rq_upto D k C C' vs vt
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?n p. run_context n C
     (vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes) =
     Abort ExHalt_abort p /\ p.vs_requests = s.vs_requests` by
    metis_tac[request_cut_clipped_abort] >>
  `?m q. run_context m C'
     (vt with vs_outcomes := TAKE (k - LENGTH vt.vs_requests) vt.vs_outcomes) =
     Abort ExHalt_abort q /\ q.vs_requests = t.vs_requests` by
    metis_tac[request_cut_clipped_abort] >>
  `LENGTH p.vs_requests = LENGTH q.vs_requests` by simp[] >>
  `LIST_REL (request_agree_except D) s.vs_requests t.vs_requests` by
    metis_tac[clipped_abort_request_history] >>
  `LENGTH s.vs_requests < LENGTH u.vs_requests /\
   LENGTH t.vs_requests < LENGTH v.vs_requests` by simp[] >>
  `?rq. u.vs_requests = s.vs_requests ++ [rq]` by
    metis_tac[recording_step_appends_one] >>
  `?rq'. v.vs_requests = t.vs_requests ++ [rq']` by
    metis_tac[recording_step_appends_one] >>
  `request_agree_except D rq rq'` by
    (qpat_x_assum `request_agree_except D (EL _ _) (EL _ _)` mp_tac >>
     simp[EL_APPEND2]) >>
  `LIST_REL (request_agree_except D) u.vs_requests v.vs_requests` by
    simp[LIST_REL_APPEND_EQ] >> simp[] >>
  `?next. raw_reachable vs C fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[raw_reachable_recording_successor] >>
  `?next'. raw_reachable vt C' fn' next' (v with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[raw_reachable_recording_successor] >>
  irule ctx_rq_upto_from_endpoints >> simp[] >>
  qexistsl_tac [`fn`, `fn'`, `next`, `next'`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`,
    `v with vs_inst_idx := SUC t.vs_inst_idx`] >>
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem request_cut_same_recording:
  EVERY wf_function C.ctx_functions /\
  raw_reachable vs C fn i s /\ i.inst_opcode <> INVOKE /\
  step_inst n C i s = OK u /\ LENGTH s.vs_requests = k /\ k < LENGTH u.vs_requests /\
  raw_reachable vs C g j t /\ j.inst_opcode <> INVOKE /\
  step_inst m C j t = OK v /\ LENGTH t.vs_requests = k /\ k < LENGTH v.vs_requests ==>
  EL k u.vs_requests = EL k v.vs_requests
Proof
  strip_tac >>
  `LENGTH s.vs_requests < LENGTH u.vs_requests /\
   LENGTH t.vs_requests < LENGTH v.vs_requests` by simp[] >>
  `?next. raw_reachable vs C fn next (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[raw_reachable_recording_successor] >>
  `?next'. raw_reachable vs C g next' (v with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[raw_reachable_recording_successor] >>
  mp_tac (Q.INST [`C` |-> `C`, `vs0` |-> `vs`,
    `fn` |-> `fn`, `inst` |-> `next`, `s` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`,
    `fn'` |-> `g`, `inst'` |-> `next'`, `t` |-> `v with vs_inst_idx := SUC t.vs_inst_idx`]
    raw_reachable_requests_comparable) >>
  simp[IS_PREFIX_APPEND] >> strip_tac >> fs[EL_APPEND1]
QED
