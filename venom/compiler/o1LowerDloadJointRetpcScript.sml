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
  (* P4a in progress *) cheat
QED
