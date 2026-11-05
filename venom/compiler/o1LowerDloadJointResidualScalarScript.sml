(* Remaining clean single-output scalar operations. *)
Theory o1LowerDloadJointResidualScalar
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointRead0 o1LowerDloadJointAssign
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadEnvironment
  ptrDiscipline pointerConfinedDefs memLocDefs unitShapeDefs o1PassContract
  venomInst venomExecSemantics venomState list finite_map

Theorem ld_joint_residual_scalar_operands_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SIGNEXTEND; BYTE; OFFSET] ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[MEM, is_pointer_preserving_op_def, mem_read_ops_def,
      mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_residual_scalar_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SIGNEXTEND; BYTE; OFFSET; INITIAL_FMP] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out x. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out x t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out x t)
Proof
  strip_tac >>
  `ld_env_agree sites fn H tn s t` by metis_tac[ld_joint_environment] >>
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- (`s.vs_initial_fmp = t.vs_initial_fmp` by
        fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[step_inst_non_invoke] >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      qexistsl_tac [`out`,`s.vs_initial_fmp`] >> simp[] >>
      irule ld_env_clean_update >> simp[] >>
      simp[occurrence_out_def, out_prov_def] >>
      irule ld_out_taint_default >> simp[]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (drule ld_joint_residual_scalar_operands_clean >> simp[] >>
     gvs[MEM] >> metis_tac[]) >>
  fs[MEM] >>
  (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
   simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[exec_pure2_def, AllCaseEqs()] >> strip_tac >>
   qpat_x_assum `update_var _ _ _ = s1` (SUBST_ALL_TAC o SYM) >>
   qmatch_goalsub_abbrev_tac `update_var out value s` >>
   qexistsl_tac [`out`,`value`] >> simp[] >>
   conj_tac >- metis_tac[MEM] >>
   irule ld_env_clean_update >> simp[] >>
   simp[occurrence_out_def, out_prov_def] >>
   irule ld_out_taint_default >> simp[])
QED

Theorem ld_joint_residual_scalar_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SIGNEXTEND; BYTE; OFFSET; INITIAL_FMP] /\
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
  strip_tac >> drule_all ld_joint_residual_scalar_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by gvs[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def, MEM] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexists_tac `update_var out x t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`x`,`x`] >>
    fs[update_var_def, venom_state_component_equality,
       ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  fs[MEM] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt (pop_assum kall_tac) >>
  namedCases_on `inst.inst_operands` ["", "h tail"] >> simp[] >>
  namedCases_on `tail` ["", "h2 tail2"] >> simp[] >>
  namedCases_on `tail2` ["", "h3 tail3"] >> simp[] >>
  Cases_on `tail3` >> simp[]
QED
