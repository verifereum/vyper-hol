Theory o1LowerDloadSuppliedSegmentNext
Ancestors
  o1LowerDloadSuppliedSegmentResources o1LowerDloadSuppliedSegmentTransport
  o1LowerDloadSuppliedSegmentControl o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadReadiness o1LowerDloadRawBridge
  o1LowerDloadOccurrenceHeadroom o1LowerDloadJointScalar
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadOpaque
  o1PassContract lowerDloadDefs ptrDiscipline contextCodegenRel
  venomExecSemantics venomExecProps venomWf venomInst venomState
  irSupply list finite_map words

Theorem ld_dloadbytes_successor_shape[local]:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOADBYTES /\ step_inst fuel C inst s = OK s1 ==>
  ?dst src sz p x z inst2.
    inst.inst_operands = [dst;src;sz] /\ inst.inst_outputs = [] /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME x /\
    eval_operand sz s = SOME z /\
    s1 = write_memory_with_expansion (w2n p)
      (TAKE (w2n z) (DROP (w2n x) s.vs_data_section ++ REPLICATE (w2n z) 0w)) s /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[wf_function_def, fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  drule_all ld_nonterminator_successor >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_joint_dloadbytes_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  mem_inv dload_offset_ok C vs /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 es t2 t3 fn' bb'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    TAKE 2 (DROP t.vs_inst_idx bb'.bb_instructions) = es /\ LENGTH es = 2 /\
    t.vs_inst_idx + 2 <= LENGTH bb'.bb_instructions /\
    step_inst fuel C' (EL 0 es) t = OK t2 /\
    step_inst fuel C' (EL 1 es) t2 = OK t3 /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t3 with vs_inst_idx := t.vs_inst_idx+2)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `wf_function fn /\ fn_inst_wf fn` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  drule_all ld_dloadbytes_successor_shape >> strip_tac >>
  drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ld_joint_segment_control >>
  disch_then drule >> disch_then drule >> simp[IgnAsm `s1 = _`] >> strip_tac >>
  `code_layout_valid t` by metis_tac[ld_joint_segment_layout] >>
  `w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256)` by
    (drule ld_joint_segment_offset >> disch_then irule >> simp[] >> metis_tac[]) >>
  Cases_on `fresh_ir_var v` >> rename1 `fresh_ir_var v = (bv,v1)` >>
  `~MEM bv v.irs_used_vars` by metis_tac[fresh_ir_var_contract] >>
  `~MEM bv (fn_ir_vars fn)` by metis_tac[] >>
  `dst <> Var bv /\ sz <> Var bv` by
    (conj_tac >> strip_tac >>
     `MEM (Var bv) inst.inst_operands` by simp[] >>
     metis_tac[ld_active_operand_ir_var]) >>
  drule_at (Pat `lower_dload_inst_supply _ _ = _`)
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_joint_supply_dloadbytes_transport)) >>
  disch_then (drule_at (Pat `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_ir_var _ = _`)) >>
  simp[IgnAsm `s1 = _`] >>
  disch_then drule >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst fuel C' (HD es) t = OK t2` >>
  qmatch_asmsub_abbrev_tac `ld_env_agree sites fn _ _ s1 t3` >>
  `step_prov PG G inst s1 = G /\ occurrence_step a HP H inst s1 = H` by
    simp[step_prov_def, occurrence_step_def, set_prov_def, DRESTRICT_UNIV] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    fs[ld_joint_boundary_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> ALLOCA` by simp[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG G (step_taint inst s s1 tn) fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexistsl_tac [`inst2`,`t2`,`t3`] >>
  simp[IgnAsm `s1 = _`, arithmeticTheory.ADD_COMM] >>
  `TAKE 2 (DROP t.vs_inst_idx bb'.bb_instructions) = es` by metis_tac[] >>
  simp[IgnAsm `s1 = _`] >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  simp[IgnAsm `s1 = _`, ld_joint_boundary_def] >>
  `fn'' = fn'` by metis_tac[optionTheory.SOME_11] >>
  `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >>
     simp[write_memory_with_expansion_def, active_inst_def]) >>
  `ld_joint_control u fn fn' (s with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := t.vs_inst_idx + 2)` by metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (qexists_tac `u'` >>
      qhdtm_assum `ld_joint_frame`
        (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
        fs[wf_function_def, fn_labels_def] >>
      qpat_x_assum `ld_joint_control u' _ _ _ _` mp_tac >>
      strip_tac >> drule_all ld_joint_control_segment >> strip_tac >>
      rename1 `lower_dload_inst_supply v2 inst = (es2,v2')` >>
      `LENGTH es2 = 2` by
        (qpat_x_assum `lower_dload_inst_supply v2 inst = _` mp_tac >>
         simp[lower_dload_inst_supply_def, AllCaseEqs()] >>
         rpt strip_tac >> gvs[]) >>
      `ld_joint_control u' fn fn'' (s with vs_inst_idx := SUC s.vs_inst_idx)
        (t with vs_inst_idx := t.vs_inst_idx + 2)` by metis_tac[] >>
      qpat_x_assum `ld_joint_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
      qpat_x_assum `!next. _` kall_tac >>
      qpat_x_assum `!next. _` kall_tac >>
      simp[IgnAsm `s1 = _`, ld_joint_frame_def] >>
      conj_tac
      >- (qpat_x_assum `ld_env_agree sites fn (occurrence_step _ _ _ _ _) _ _ _` mp_tac >>
          simp[IgnAsm `s1 = _`, ld_env_agree_def, op_taint_def]) >>
      fs[IgnAsm `s1 = _`, ld_params_agree_def, ld_joint_local_fields_def,
         ld_joint_allocas_def] >>
      simp[Abbr `t3`, Abbr `t2`, write_memory_with_expansion_def,
          update_var_def, ld_params_agree_def, ld_joint_local_fields_def,
          ld_joint_allocas_def] >>
      qpat_x_assum `ld_joint_control u' _ _ (_ with vs_inst_idx := _) _` mp_tac >>
      simp[NoAsms, ld_joint_control_def, write_memory_with_expansion_def,
           update_var_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[Abbr `t3`, Abbr `t2`, write_memory_with_expansion_def,
      update_var_def, ld_shared_agree_def, step_taint_def,
      set_var_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
      DRESTRICT_UNIV]
QED
