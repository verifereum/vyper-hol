(* Structural boundary for combined memory, immutable and log effects. *)
Theory o1LowerDloadJointInternalEffects
Ancestors
  o1LowerDloadJointStorageWrite o1LowerDloadJointMemoryWrite
  o1LowerDloadJointRangeRead o1LowerDloadJointAssign o1LowerDloadShared
  o1LowerDloadJointRelation o1LowerDloadEnvironment o1LowerDloadOccurrence
  ptrDiscipline venomState venomExecSemantics venomInst
  finite_map list pred_set unitShapeDefs o1PassContract venomWf codegenRel contextCodegenRel

Theorem ld_joint_internal_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|> /\
  t1 = t with <|vs_memory := mt; vs_immutables := imt; vs_logs := lt|> /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G1 tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H1 /\
  occurrence_annotation_ok n a U B HP H1 stk PG G1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_env_agree sites fn H1 tn1 s1 t1 /\
  ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn1 s1 t1 ==>
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

(* Check that both concrete effect shapes enter the combined boundary;
   payload relations remain semantic obligations, not framing assumptions. *)
Theorem ld_internal_effect_update_shapes[local]:
  (?ms ims ls. istore off v s =
     s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|>) /\
  (?ms ims ls. (s with vs_logs := s.vs_logs ++ [ev]) =
     s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|>)
Proof
  conj_tac
  >- (qexistsl_tac [`(mstore off v s).vs_memory`,
                   `s.vs_immutables |+ (off,v)`,`s.vs_logs`] >>
      simp[istore_def, mstore_def, venom_state_component_equality]) >>
  qexistsl_tac [`s.vs_memory`,`s.vs_immutables`,`s.vs_logs ++ [ev]`] >>
  simp[venom_state_component_equality]
QED
