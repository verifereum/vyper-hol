(* Masked storage and transient reads at source instruction boundaries. *)
Theory o1LowerDloadJointStorageRead
Ancestors
  o1LowerDloadJointScalar o1LowerDloadJointAssign o1LowerDloadShared
  o1LowerDloadJointRelation o1LowerDloadJointMemoryRead o1LowerDloadJointShift
  o1LowerDloadMemoryConsumer o1LowerDloadEnvironment o1LowerDloadOccurrence
  o1LowerDloadRelocationKernel ptrDiscipline pointerConfinedDefs
  venomState venomExecSemantics venomInst memLocDefs unitShapeDefs
  list pred_set finite_map words codegenRel contextCodegenRel o1PassContract

Theorem ld_joint_storage_key_clean[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SLOAD; TLOAD] ==>
  !op. MEM op inst.inst_operands ==>
    op_prov H op = NONE /\ op_taint tn op = {} /\
    eval_operand op s = eval_operand op t
Proof
  strip_tac >> drule ld_joint_scalar_operands_clean >>
  gvs[is_pointer_preserving_op_def, mem_read_ops_def,
    mem_write_ops_def, retpc_use_ok_def, taint_ok_def] >> metis_tac[]
QED

Theorem ld_joint_storage_load_step[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SLOAD; TLOAD] /\ step_inst fuel C inst s = OK s1 ==>
  ?out x y. s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[ld_joint_storage_key_clean] >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[ld_joint_boundary_def] >>
  gvs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_def] >>
  simp[exec_read1_def, AllCaseEqs()] >>
  (strip_tac >> gvs[] >>
   rename1 `inst.inst_outputs = [out]` >>
   qmatch_goalsub_abbrev_tac `step_taint inst s (update_var out value s) tn` >>
   `?value'. step_inst fuel C' inst t = OK (update_var out value' t) /\
      word_agree_except (out_taint tn inst s) value value'` by
     (simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def] >>
      gvs[Abbr `value`, out_taint_def, sload_def, tload_def,
          ld_shared_agree_def, key_taint_def, word_agree_except_def,
          contract_storage_def, contract_transient_def,
          vfmStateTheory.lookup_account_def, vfmStateTheory.lookup_storage_def] >>
      qpat_x_assum `SOME _ = eval_operand _ _` (SUBST_ALL_TAC o SYM) >>
      simp[] >> metis_tac[]) >>
   qexistsl_tac [`out`,`value`,`value'`] >> conj_tac
   >- simp[Abbr `value`] >>
   conj_tac
   >- (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM) >>
       qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
       simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def]) >>
   irule ld_env_masked_update >> simp[] >>
   conj_tac >- simp[occurrence_out_def, out_prov_def] >>
   metis_tac[ld_joint_environment])
QED

Theorem ld_joint_storage_load_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [SLOAD; TLOAD] /\ step_inst fuel C inst s = OK s1 /\
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
  strip_tac >> drule_all ld_joint_storage_load_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by gvs[MEM] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[MEM, is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[MEM]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[MEM]) >>
  qexists_tac `update_var out y t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac >- (qexistsl [`out`,`s.vs_gas_readings`,`x`,`y`] >>
    fs[update_var_def, venom_state_component_equality,
       ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  gvs[MEM] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss] >>
  rpt (CASE_TAC >> simp[])
QED
