Theory o1LowerDloadFreshNext
Ancestors
  o1LowerDloadAllocationBoundary o1LowerDloadJointAllocation
  o1LowerDloadJointRelation o1LowerDloadJointAssign
  o1LowerDloadOccurrence o1LowerDloadPairedAllocation
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadRelocationKernel ptrDiscipline
  venomExecSemantics venomState codegenRel finite_map words list pred_set arithmetic
  o1PassContract venomWf venomInst contextCodegenRel

Theorem ld_alloca_fresh_annotations[local]:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit amount] /\
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK s1 ==>
  occurrence_sites_step a B inst s1 =
    B |+ ((a,inst.inst_id),(s.vs_alloca_next,w2n amount)) /\
  occurrence_step a HP H inst s1 = H |+ (out,(a,inst.inst_id)) /\
  step_taint inst s s1 tn = tn with
    <|t_var := tn.t_var |+ (out,{});
      t_mem := tn.t_mem UNION {s.vs_alloca_next+j | j < w2n amount}|>
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (Q.ISPEC `amount:bytes32`
    (Q.GEN `amount` (SPEC_ALL lower_dload_alloca_fresh))) >>
  disch_then (qspec_then `amount` strip_assume_tac) >> gvs[] >>
  simp[occurrence_sites_step_def, occurrence_step_def, occurrence_out_def,
       set_prov_def, update_var_def, FLOOKUP_UPDATE,
       step_taint_def, mem_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, adopt_reset_def, imm_taint_def,
       new_site_bytes_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def] >>
  `inst.inst_id NOTIN FDOM s.vs_allocas` by gvs[FLOOKUP_DEF] >>
  simp[] >>
  simp[taint_component_equality, EXTENSION] >>
  rpt gen_tac >> eq_tac
  >- (rpt strip_tac >> gvs[] >> Cases_on `inst.inst_id = aid` >>
      gvs[FLOOKUP_DEF] >> disj2_tac >>
      qexists_tac `x - s.vs_alloca_next` >> decide_tac) >>
  rpt strip_tac >> gvs[] >> disj2_tac >>
  qexistsl_tac [`inst.inst_id`, `s.vs_alloca_next`, `w2n amount`] >>
  simp[] >> decide_tac
QED

Theorem ld_joint_alloca_fresh_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  mem_inv dload_headroom_ok C vs /\ callee_first names C.ctx_functions /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out] /\
  MEM inst.inst_id (fn_ir_inst_ids fn) /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U (occurrence_sites_step a B inst s1) HP
      (occurrence_step a HP H inst s1)
      (sites |+ ((a,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n amount))) X ts
Proof
  strip_tac >> drule_all ld_joint_alloca_fresh_metadata >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all occ_frame_reachable_next >> strip_tac >>
  `occurrence_annotation_ok n a U (occurrence_sites_step a B inst s1) HP
      (occurrence_step a HP H inst s1) stk PG (step_prov PG G inst s1)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[]) >>
  `exec_alloca inst s amount = OK s1 /\ exec_alloca inst t amount = OK t1` by
    metis_tac[lower_dload_step_alloca] >>
  drule_all ld_alloca_fresh_annotations >> strip_tac >>
  `FLOOKUP t.vs_allocas inst.inst_id = NONE` by
    metis_tac[ld_joint_original_lookup] >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> first_x_assum drule >>
     simp[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `(a,inst.inst_id) NOTIN FDOM sites` by
    (`FLOOKUP B (a,inst.inst_id) = NONE` by
       fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
     fs[ld_joint_erasure_def, FLOOKUP_DEF]) >>
  `~MEM a (MAP (\f. f.of_owner) U)` by fs[occurrence_annotation_ok_def] >>
  `ld_joint_saved C' (sites |+ ((a,inst.inst_id),
      (s.vs_alloca_next,t.vs_alloca_next,w2n amount))) X lo U stk ts` by
    (irule ld_joint_saved_extend >> simp[]) >>
  `ld_env_agree sites fn H tn s t` by metis_tac[ld_joint_environment] >>
  drule_at (Pat `ld_env_agree _ _ _ _ _ _`)
    (Q.ISPEC `amount:bytes32` (Q.GEN `alloc_size` (SPEC_ALL ld_alloca_fresh))) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `amount` mp_tac) >>
  strip_tac >> gvs[] >>
  `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >>
     gvs[exec_alloca_def, update_var_def, active_inst_def]) >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  drule_all ld_joint_control_unchanged_next >> strip_tac >>
  `ld_joint_control u fn fn'
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_x_assum `ld_joint_control u fn fn' (_ with vs_inst_idx := _) _` mp_tac >>
     gvs[exec_alloca_def, update_var_def, ld_joint_control_def]) >>
  qexists_tac `u` >> simp[] >>
  simp[ld_joint_boundary_def] >>
  reverse conj_tac
  >- (gvs[exec_alloca_def, update_var_def, ld_shared_agree_def]) >>
  qexists_tac `u` >> simp[ld_joint_frame_def] >>
  conj_tac
  >- (qpat_x_assum `ld_env_agree (_ |+ _) fn _ tn s1 t1` mp_tac >>
      simp[ld_env_agree_def, op_taint_def, FLOOKUP_UPDATE] >>
      strip_tac >>
      rpt strip_tac >> Cases_on `v = out`
      >- (gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE] >>
          pure_rewrite_tac[ld_value_agree_pointer] >>
          simp[FLOOKUP_UPDATE] >>
          metis_tac[WORD_ADD_SUB2]) >>
      fs[] >> metis_tac[]) >>
  conj_tac >- gvs[ld_params_agree_def] >>
  conj_tac >- gvs[exec_alloca_def, update_var_def, ld_joint_local_fields_def] >>
  conj_tac
  >- (qpat_x_assum `ld_joint_allocas (_ |+ _) X a fn t1` mp_tac >>
      simp[NoAsms, ld_joint_allocas_def] >> strip_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `aid = inst.inst_id` >>
      gvs[FLOOKUP_UPDATE] >> first_x_assum drule >> strip_tac >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED
