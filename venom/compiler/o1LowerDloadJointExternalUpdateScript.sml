(* Common structural boundary for external-call state updates. *)
Theory o1LowerDloadJointExternalUpdate
Ancestors
  o1LowerDloadJointInternalEffects o1LowerDloadJointRelation
  o1LowerDloadEnvironment o1LowerDloadOccurrence o1LowerDloadJointScalar
  o1LowerDloadJointAssign pointerConfinedDefs
  o1LowerDloadShared ptrDiscipline venomState venomExecSemantics venomInst
  finite_map list unitShapeDefs o1PassContract venomWf contextCodegenRel

Theorem ld_joint_external_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with <|vs_vars := es; vs_memory := ms; vs_accounts := acs;
    vs_transient := trs; vs_logs := ls; vs_outcomes := os;
    vs_requests := rqs; vs_pending_deletions := pds; vs_returndata := rds|> /\
  t1 = t with <|vs_vars := et; vs_memory := mt; vs_accounts := act;
    vs_transient := trt; vs_logs := lt; vs_outcomes := ot;
    vs_requests := rqt; vs_pending_deletions := pdt; vs_returndata := rdt|> /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G1 tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H1 /\
  occurrence_annotation_ok n a U B HP H1 stk PG G1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_env_agree sites fn H1 tn1 s1 t1 /\
  ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn1 s1 t1 /\
  s1.vs_returndata = t1.vs_returndata ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G1 tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H1 sites X ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> drule occ_frame_reachable_annotation >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >> simp[active_inst_def]) >>
  drule_all ld_joint_control_unchanged_next >> strip_tac >>
  qexistsl_tac [`u`,`fn'`] >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `t1 = _` SUBST_ALL_TAC >>
  gvs[venom_state_fupdcanon] >>
  simp[ld_joint_boundary_def, venom_state_fupdcanon] >> conj_tac
  >- (qexists_tac `u` >>
      gvs[ld_joint_frame_def, ld_params_agree_def, ld_joint_local_fields_def,
          ld_joint_allocas_def, ld_env_agree_def, op_taint_def] >>
      conj_tac
      >- (qpat_x_assum `ld_joint_control _ _ _ (_ with vs_inst_idx := _) _` mp_tac >>
          simp[NoAsms, ld_joint_control_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
      rpt strip_tac >> metis_tac[]) >>
  gvs[ld_shared_agree_def]
QED
