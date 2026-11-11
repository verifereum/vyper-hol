(* Opaque return-token writes need availability, not numeric equality. *)
Theory o1LowerDloadJointRetpc
Ancestors
  o1LowerDloadJointAssign unitShapeDefs o1LowerDloadEnvironment
  o1LowerDloadOccurrence ptrDiscipline venomState finite_map list
  venomExecSemantics venomExecProps o1LowerDloadJointRelation o1PassContract
  venomInst contextCodegenRel

Theorem ld_env_retpc_update:
  ld_env_agree sites fn H tn s t /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [out] ==>
  ld_env_agree sites fn (occurrence_step a HP H inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn)
    (update_var out x s) (update_var out y t)
Proof
  strip_tac >>
  `retpc_var fn out` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >>
     qexists_tac `inst` >> simp[]) >>
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE,
       occurrence_step_def, occurrence_out_def, out_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `out = v` >> gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `out = v` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      ld_env_agree_def, op_taint_def]
QED

Theorem ld_retpc_success_iff:
  inst.inst_opcode = RETPC_PARAM ==>
  (step_inst fuel C inst s = OK s1 <=>
   ?idx out. inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
     s1 = update_var out s.vs_return_pc_token s)
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_retpc_error_iff:
  inst.inst_opcode = RETPC_PARAM ==>
  (step_inst fuel C inst s = Error e <=> step_inst fuel C' inst t = Error e)
Proof
  strip_tac >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()]
QED

Theorem ld_joint_retpc_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\ step_inst fuel C inst s = OK s1 ==>
  ?out. inst.inst_outputs = [out] /\
    s1 = update_var out s.vs_return_pc_token s /\
    step_inst fuel C' inst t = OK (update_var out t.vs_return_pc_token t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out t.vs_return_pc_token t)
Proof
  strip_tac >>
  `?idx out. inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
     s1 = update_var out s.vs_return_pc_token s` by
    metis_tac[ld_retpc_success_iff] >>
  qexists_tac `out` >> simp[] >> conj_tac
  >- (simp[ld_retpc_success_iff] >> metis_tac[]) >>
  irule ld_env_retpc_update >> simp[] >>
  conj_tac
  >- (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
      metis_tac[MEM_EL]) >>
  metis_tac[ld_joint_environment]
QED

Theorem ld_joint_retpc_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ inst.inst_opcode = RETPC_PARAM /\
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
  strip_tac >>
  `?idx. inst.inst_operands = [Lit idx]` by
    metis_tac[ld_retpc_success_iff] >>
  drule_all ld_joint_retpc_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES]` by simp[] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def]) >>
  qexists_tac `update_var out t.vs_return_pc_token t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac
  >- (qexistsl [`out`,`s.vs_gas_readings`,`s.vs_return_pc_token`,`t.vs_return_pc_token`] >>
      fs[update_var_def, venom_state_component_equality,
         ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss]
QED
