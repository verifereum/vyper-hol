(* Successful identity-state operations and PC-only boundary transport. *)
Theory o1LowerDloadJointIdentity
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointAssign o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadEnvironment o1LowerDloadShared ptrDiscipline
  pointerConfinedDefs memLocDefs unitShapeDefs o1PassContract venomWf contextCodegenRel
  venomInst venomExecSemantics venomState list finite_map

Theorem ld_joint_identity_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] /\
  step_inst fuel C inst s = OK s1 ==>
  s1 = s /\ step_inst fuel C' inst t = OK t
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (drule ld_joint_scalar_operands_clean >>
     gvs[MEM, is_pointer_preserving_op_def, mem_read_ops_def,
         mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]) >>
  fs[MEM] >>
  (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
   simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[AllCaseEqs()] >> strip_tac >> gvs[] >> metis_tac[MEM])
QED

Theorem ld_joint_identity_boundary_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G tn fn inst2
    (s with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H /\
  occurrence_annotation_ok n a U B HP H stk PG G
    (s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G tn fn inst2
      (s with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC t.vs_inst_idx) n a U B HP H sites X ts
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
  drule_all ld_joint_control_unchanged_next >> strip_tac >>
  qexistsl_tac [`u`,`fn'`] >> simp[] >>
  simp[ld_joint_boundary_def] >> conj_tac
  >- (qexists_tac `u` >>
      gvs[ld_joint_frame_def, ld_params_agree_def, ld_joint_local_fields_def,
          ld_joint_allocas_def, ld_env_agree_def, op_taint_def] >>
      qpat_x_assum `ld_joint_control _ _ _ (_ with vs_inst_idx := _) _` mp_tac >>
      simp[NoAsms, ld_joint_control_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[ld_shared_agree_def]
QED

Theorem ld_joint_identity_annotations:
  inst_wf inst /\ MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] ==>
  step_prov PG G inst s = G /\ occurrence_step a HP H inst s = H /\
  step_taint inst s s tn = tn
Proof
  strip_tac >>
  `inst.inst_outputs = []` by
    (fs[MEM] >> gvs[inst_wf_def]) >>
  Cases_on `tn` >> fs[MEM] >>
  simp[step_prov_def, occurrence_step_def, step_taint_def,
       mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       new_site_bytes_def, written_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, range_bytes_def,
       FLOOKUP_DEF, set_prov_def, set_var_taint_def, DRESTRICT_UNIV, taint_component_equality, SF CONJ_ss] >>
  rpt (pop_assum kall_tac) >>
  namedCases_on `inst.inst_operands` ["", "h tail"] >> simp[] >>
  namedCases_on `tail` ["", "h2 tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "h3 tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[]
QED

Theorem ld_joint_identity_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [NOP; ASSERT; ASSERT_UNREACHABLE] /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >> drule_all ld_joint_identity_step >> strip_tac >> gvs[] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `inst_wf inst` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> first_x_assum drule >>
     simp[o1_fn_shape_def] >> strip_tac >>
     fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `step_prov PG G inst s = G /\ occurrence_step a HP H inst s = H /\
   step_taint inst s s tn = tn` by
    (irule ld_joint_identity_annotations >> simp[]) >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by gvs[MEM] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def, MEM] >>
  `occ_frame_reachable vs C stk PG G tn fn inst2
     (s with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G
     (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  simp[] >>
  irule ld_joint_identity_boundary_next >> simp[] >> metis_tac[]
QED

Theorem ld_joint_assert_abort:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  step_inst fuel C inst s = Abort ab s1 ==>
  ?t1. step_inst fuel C' inst t = Abort ab t1 /\
    dead_result_rel D (Abort ab s1) (Abort ab t1)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (drule ld_joint_scalar_operands_clean >>
     gvs[MEM, is_pointer_preserving_op_def, mem_read_ops_def,
         mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]) >>
  fs[MEM] >>
  (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
   simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
   simp[dead_result_rel_def] >> metis_tac[MEM])
QED
