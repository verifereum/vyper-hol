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
  (* P4a in progress *) cheat
QED
