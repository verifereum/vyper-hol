Theory o1LowerDloadRepeatedNext
Ancestors
  o1LowerDloadJointAssign o1LowerDloadJointAllocation
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadPairedAllocation
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadRelocationKernel
  ptrDiscipline venomExecSemantics venomState codegenRel contextCodegenRel
  finite_map words list pred_set arithmetic o1PassContract venomInst

Theorem ld_alloca_repeated_annotations[local]:
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  inst.inst_operands = [Lit amount] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) ==>
  occurrence_sites_step a B inst (update_var out (n2w b) s) = B /\
  occurrence_step a HP H inst (update_var out (n2w b) s) =
    H |+ (out,(a,inst.inst_id)) /\
  step_taint inst s (update_var out (n2w b) s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `FLOOKUP B (a,inst.inst_id) = SOME (b,z)` by
    fs[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  simp[occurrence_sites_step_def, occurrence_step_def, occurrence_out_def,
       set_prov_def, update_var_def, FLOOKUP_UPDATE,
       step_taint_def, mem_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, adopt_reset_def, imm_taint_def,
       new_site_bytes_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def, SF CONJ_ss] >>
  conj_tac
  >- (simp[fmap_eq_flookup, FLOOKUP_UPDATE] >> gen_tac >>
      Cases_on `x = (a,inst.inst_id)` >> gvs[]) >>
  simp[FLOOKUP_DEF, taint_component_equality, EXTENSION, SF CONJ_ss]
QED

Theorem ld_joint_alloca_repeated_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,z) /\
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
  strip_tac >> drule_all ld_joint_original_site >> strip_tac >>
  `exec_alloca inst s amount = OK s1` by metis_tac[lower_dload_step_alloca] >>
  `s1 = update_var out (n2w b) s` by gvs[exec_alloca_def] >>
  `step_inst fuel C' inst t = OK (update_var out (n2w c) t)` by
    (drule_all lower_dload_step_alloca >>
     disch_then (fn th => rewrite_tac[th]) >> simp[exec_alloca_def]) >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  drule_all ld_alloca_repeated_annotations >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[]) >>
  `ld_env_agree sites fn H tn s t` by metis_tac[ld_joint_environment] >>
  `ld_params_agree sites HP s t /\
   ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
   ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   t.vs_alloca_next = s.vs_alloca_next +
     32 * CARD {id | id IN FDOM X /\ MEM (FST id) (a::MAP (\f. f.of_owner) U)}` by
    gvs[ld_joint_boundary_def, ld_joint_frame_def] >>
  drule_all
    (Q.ISPEC `amount:bytes32` (Q.GEN `alloc_size` (SPEC_ALL ld_alloca_repeated))) >>
  disch_then (qspec_then `amount` mp_tac) >> strip_tac >>
  `ld_env_agree sites fn (occurrence_step a HP H inst s1)
    (step_taint inst s s1 tn) s1 (update_var out (n2w c) t)` by
    (gvs[exec_alloca_def] >>
     qpat_x_assum `ld_env_agree sites fn (_ |+ _) tn _ _` mp_tac >>
     simp[ld_env_agree_def, op_taint_def, update_var_def, FLOOKUP_UPDATE] >>
     strip_tac >> rpt strip_tac >> Cases_on `v = out`
     >- (gvs[] >> pure_rewrite_tac[ld_value_agree_pointer] >>
         qexistsl_tac [`b`,`c`,`z`] >> simp[WORD_ADD_SUB2]) >>
     fs[] >> metis_tac[]) >>
  qexists_tac `update_var out (n2w c) t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >> gvs[] >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`n2w b`,`n2w c`] >>
    fs[update_var_def, venom_state_component_equality,
       ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[]
QED
