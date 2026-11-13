(* Whole-boundary PARAM preservation with relocated parameter values. *)
Theory o1LowerDloadJointParam
Ancestors
  o1LowerDloadJointAssign o1LowerDloadEnvironment o1LowerDloadJointRelation
  venomExecSemantics venomExecProps ptrDiscipline o1LowerDloadOccurrence
  finite_map list venomState o1PassContract venomInst

Theorem ld_param_success_iff:
  inst.inst_opcode = PARAM ==>
  (step_inst fuel C inst s = OK s1 <=>
   ?idx out. inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
     w2n idx < LENGTH s.vs_params /\
     s1 = update_var out (EL (w2n idx) s.vs_params) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ld_env_param_update:
  ld_env_agree sites fn H tn s t /\ ld_params_agree sites HP s t /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ w2n idx < LENGTH s.vs_params ==>
  ld_env_agree sites fn
    (occurrence_step a HP H inst (update_var out (EL (w2n idx) s.vs_params) s))
    (step_taint inst s (update_var out (EL (w2n idx) s.vs_params) s) tn)
    (update_var out (EL (w2n idx) s.vs_params) s)
    (update_var out (EL (w2n idx) t.vs_params) t)
Proof
  strip_tac >> drule_all ld_params_element >> strip_tac >>
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE,
       occurrence_step_def, occurrence_out_def, out_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `out = v` >> gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `out = v`
  >- (gvs[] >> Cases_on `w2n idx < LENGTH HP` >>
      gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
      Cases_on `EL (w2n idx) HP` >>
      gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `w2n idx < LENGTH HP` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ld_env_agree_def, op_taint_def] >>
  Cases_on `EL (w2n idx) HP` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ld_env_agree_def]
QED

Theorem ld_joint_param_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ inst.inst_opcode = PARAM /\
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
  `?idx out. inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
    w2n idx < LENGTH s.vs_params /\
    s1 = update_var out (EL (w2n idx) s.vs_params) s` by
    metis_tac[ld_param_success_iff] >>
  `ld_params_agree sites HP s t` by
    fs[ld_joint_boundary_def, ld_joint_frame_def] >>
  `LENGTH s.vs_params = LENGTH t.vs_params` by fs[ld_params_agree_def] >>
  `ld_env_agree sites fn H tn s t` by metis_tac[ld_joint_environment] >>
  drule_all ld_env_param_update >> strip_tac >>
  `step_inst fuel C' inst t = OK (update_var out (EL (w2n idx) t.vs_params) t)` by
    (simp[ld_param_success_iff] >> metis_tac[]) >>
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
  qexists_tac `update_var out (EL (w2n idx) t.vs_params) t` >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  irule ld_joint_var_update_next >> simp[] >>
  conj_tac
  >- (qexistsl [`out`,`s.vs_gas_readings`,`EL (w2n idx) s.vs_params`,`EL (w2n idx) t.vs_params`] >>
      fs[update_var_def, venom_state_component_equality,
         ld_joint_boundary_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[] >>
  simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, update_var_def, new_site_bytes_def, written_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF, SF CONJ_ss]
QED
